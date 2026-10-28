-- Prove2me | solution 1 for OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:38:31.27269+00:00
-- url     : https://prove2.me/submissions/31c082a6-0400-4dbd-b67e-9579d16f6109

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_PreparedRow_geometric_row_probability

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_LargeCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpLogRamsey.MomentBudgetBridge

lemma anchorBudget_nonneg (p : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ anchorBudget p P := by
  unfold anchorBudget
  positivity

end SharpLogRamsey.MomentBudgetBridge
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PencilGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Classical

namespace SharpLogRamsey.PreparedProjectiveGeometry
open SharpLogRamsey.CertificateGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma point_dualCoannihilator (H : Projectivization K (Module.Dual K V)) :
    H.submodule.dualCoannihilator = LinearMap.ker H.rep := by
  apply SetLike.coe_injective
  rw [H.submodule_eq, Submodule.coe_dualCoannihilator_span]
  ext v
  simp

omit [Finite K] in
theorem overlap_plane_zero (hdim : Module.finrank K V = 3)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ)
    (H J : Projectivization K (Module.Dual K V)) (hne : H ≠ J)
    (hxH : x.submodule ≤ LinearMap.ker H.rep) (hxJ : x.submodule ≤ LinearMap.ker J.rep) :
    overlap S x c H J = 0 := by
  have hr := finrank_join H J hne
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (H.submodule ⊔ J.submodule : Submodule K (Module.Dual K V))
  rw [Submodule.dualCoannihilator_sup_eq, point_dualCoannihilator,
    point_dualCoannihilator] at hd
  have hdim' : Module.finrank K (LinearMap.ker H.rep ⊓ LinearMap.ker J.rep : Submodule K V) = 1 := by omega
  have he : x.submodule = LinearMap.ker H.rep ⊓ LinearMap.ker J.rep :=
    Submodule.eq_of_le_of_finrank_eq (le_inf hxH hxJ) (x.finrank_submodule.trans hdim'.symm)
  have hfilter : S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro y _ h
    apply h.1
    apply Projectivization.submodule_injective
    apply Submodule.eq_of_le_of_finrank_eq
    · exact h.2.trans he.ge
    · exact y.finrank_submodule.trans x.finrank_submodule.symm
  unfold overlap
  rw [hfilter]
  simp

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestPointTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpLogRamsey.PoissonGrouping
open Classical
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma sum_hasLaw (rate : ι → ℝ≥0) (S : Finset ι) :
    HasLaw (fun ω : ι → ℕ => ∑ i ∈ S, ω i) (poissonMeasure (∑ i ∈ S, rate i)) (law rate) := by
  have hi : iIndepFun (fun i (ω : ι → ℕ) => ω i) (law rate) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have he (i : ι) : HasLaw (fun ω : ι → ℕ => ω i) (poissonMeasure (rate i)) (law rate) :=
    (measurePreserving_eval (fun i => poissonMeasure (rate i)) i).hasLaw
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_const, measure_univ, one_smul]
    symm
    apply Measure.ext_of_singleton
    intro n
    rw [poissonMeasure_singleton]
    cases n <;> simp
  | @insert i S hiS ih =>
    have ih' : HasLaw (∑ j ∈ S, fun ω : ι → ℕ => ω j)
        (poissonMeasure (∑ j ∈ S, rate j)) (law rate) := by
      convert ih using 1
      all_goals try with_reducible_and_instances rfl
      ext ω
      simp
    simp only [Finset.sum_insert hiS]
    convert (hi.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i) hiS).symm.hasLaw_add_poissonMeasure
        (he i) ih' using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp

end
end SharpLogRamsey.PoissonGrouping

open MeasureTheory
open scoped BigOperators Classical
namespace SharpLogRamsey.BoundedProbability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem real_markov (Y : Ω → ℝ) (hY : Integrable Y μ) (hy : ∀ ω,0 ≤ Y ω)
    (t : ℝ) (_ht : 0  ≤  t) (hE : MeasurableSet {ω | t ≤ Y ω}) :
    t*μ.real {ω | t ≤ Y ω}  ≤  ∫ ω,Y ω ∂μ := by
  have hi := (integrable_const t).indicator hE (μ:=μ)
  have hp : ∀ ω,({ω | t ≤ Y ω}.indicator (fun _ : Ω =>  t)) ω  ≤  Y ω := by
    intro ω
    by_cases he : t ≤ Y ω
    · simp [he]
    · simpa [he] using hy ω
  have hh := integral_mono hi hY hp
  rw [integral_indicator_const _ hE] at hh
  simpa only [smul_eq_mul,mul_comm] using hh

end
end SharpLogRamsey.BoundedProbability

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

attribute [local instance] OAI.SharpLogRamsey.ProjectiveDuality.flat_JoinedTestLearningIncidence_1
theorem dual_variance_le {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ) :
    (∑ x : Projectivization K V,
      ((∑ H, if SharpLogRamsey.Incidence.Incident x H then w H else 0) -
        (∑ i ∈ range (n+2), (Nat.card K:ℝ)^i) /
        (∑ i ∈ range (n+3), (Nat.card K:ℝ)^i) * ∑ H, w H)^2) ≤
      (Nat.card K:ℝ)^(n+1) * ∑ H,w H^2 := by
  have hh := projective_variance_le
    (show Module.finrank K (Module.Dual K V)=n+3 from Subspace.dual_finrank_eq.trans hdim) w
  rw [← (bidual (K:=K) (V:=V)).sum_comp] at hh
  simpa only [weightedIncidences,incident_bidual] using hh

end
end SharpLogRamsey.ProjectiveDuality

namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence SharpLogRamsey.ProjectiveDuality
noncomputable section
variable {A : Type*} [Fintype A]

lemma square_tail_card (f : A → ℝ) (μ t V : ℝ) (ht : 0 ≤ t)
    (hv : ∑ x,(f x-μ)^2 ≤ V) :
    ((univ.filter (fun x => μ+t ≤ f x)).card:ℝ)*t^2 ≤ V := by
  calc
    _ = ∑ x ∈ univ.filter (fun x => μ+t ≤ f x), t^2 := by simp
    _ ≤ ∑ x ∈ univ.filter (fun x => μ+t ≤ f x), (f x-μ)^2 := by
      apply sum_le_sum
      intro x hx
      have hh := (mem_filter.mp hx).2
      nlinarith
    _ ≤ ∑ x,(f x-μ)^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hv

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem pencil_weight_tail {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ)
    (hw : ∀ H, 0≤w H) (hw1 : ∀ H,w H≤1)
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ i ∈ range (n+2),(Nat.card K:ℝ)^i) /
      (∑ i ∈ range (n+3),(Nat.card K:ℝ)^i) * ∑ H,w H ≤ T/2) :
    ((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w H else 0)).card:ℝ) * (T/2)^2 ≤
        (Nat.card K:ℝ)^(n+1) * ∑ H,w H := by
  let μ := (∑ i ∈ range (n+2),(Nat.card K:ℝ)^i) /
      (∑ i ∈ range (n+3),(Nat.card K:ℝ)^i) * ∑ H,w H
  have hnorm : ∑ H,w H^2 ≤ ∑ H,w H := by
    apply sum_le_sum
    intro H _
    nlinarith [hw H,hw1 H]
  have hv := (dual_variance_le hdim w).trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have ht := square_tail_card (fun x : Projectivization K V =>
    ∑ H,if SharpLogRamsey.Incidence.Incident x H then w H else 0) μ (T/2) _ (by positivity) hv
  apply le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card ?_))
    (sq_nonneg _)) ht
  intro x hx
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have hh := (mem_filter.mp hx).2
  dsimp [μ]
  linarith

theorem pencil_family_tail {ι : Type*} [Fintype ι] {n : ℕ}
    (hdim : Module.finrank K V=n+3)
    (w : ι → Projectivization K (Module.Dual K V) → ℝ)
    (hw : ∀ i H,0≤w i H) (hw1 : ∀ i H,w i H≤1)
    (T : ℝ) (hT : 0≤T)
    (hmean : ∀ i,(∑ k ∈ range (n+2),(Nat.card K:ℝ)^k) /
      (∑ k ∈ range (n+3),(Nat.card K:ℝ)^k) * ∑ H,w i H ≤ T/2) :
    ((univ.biUnion (fun i => univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0))).card:ℝ) * (T/2)^2 ≤
        (Nat.card K:ℝ)^(n+1) * ∑ i,∑ H,w i H := by
  calc
    _ ≤ (∑ i,((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0)).card:ℝ)) * (T/2)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast (card_biUnion_le : _ ≤ ∑ i,_)
    _ = ∑ i,((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0)).card:ℝ)*(T/2)^2 := by rw [sum_mul]
    _ ≤ ∑ i,(Nat.card K:ℝ)^(n+1) * ∑ H,w i H :=
      sum_le_sum (fun i _ => pencil_weight_tail hdim (w i) (hw i) (hw1 i) T hT (hmean i))
    _ = _ := by rw [mul_sum]

end
end SharpLogRamsey.RegularPencils

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_SparseProductSharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
variable [Fintype (Projectivization K (Module.Dual K V))]

lemma sparse_smaller_square {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (hsmall : S.card≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K)) :
    (S.card:ℝ)^2≤2*(Nat.card K:ℝ)^(n+3) := by
  have hh : (S.card:ℝ)≤T.card := by exact_mod_cast hsmall
  calc
    _ = (S.card:ℝ)*S.card := pow_two _
    _ ≤ (S.card:ℝ)*T.card := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ _ := sparse_product_bound_two hdim S T hsparse

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_SparsePencilBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators

lemma geom_sum_le_twice_pow (q : ℝ) (hq : 2≤q) (n : ℕ) :
    (∑ i∈range (n+1),q^i)≤2*q^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hh : 2*q^n≤q^(n+1) := by
      rw [pow_succ]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hq (show 0≤q^n by positivity)
    linarith

lemma scalar_pencil_card (q s : ℝ) (hq : 2≤q) (hs : 0 < s) (j : ℕ) (hj : 1≤j)
    (hsmall : s^2≤2*q^(j+1)) :
    (∑ i∈range j,q^i)≤4*(q^j/s)^2 := by
  have hq0 : 0≤q := by linarith
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hj
  have hcount : (∑ i∈range (1+m),q^i)≤2*q^m := by
    simpa [Nat.add_comm] using geom_sum_le_twice_pow q hq m
  have hmul := mul_le_mul hcount hsmall (sq_nonneg s) (by positivity : 0≤2*q^m)
  have he : (2*q^m)*(2*q^(1+m+1))=4*(q^(1+m))^2 := by ring
  rw [he] at hmul
  rw [div_pow, ←mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
  exact hmul

lemma scalar_direction_two (q s : ℝ) (hq : 2≤q) (hs : 0 < s)
    (hsmall : s^2≤2*q^3) : (1:ℝ)≤4*(q^2/s) := by
  have hq0 : 0≤q := by linarith
  have hq2 : 0≤q^2 := sq_nonneg q
  have hsle : s≤4*q^2 := by
    have hpow : 2*q^3≤16*(q^2)^2 := by
      nlinarith [mul_nonneg (show 0≤q^3 by positivity) (show 0≤q-1 by linarith)]
    nlinarith [hsmall,hpow,sq_nonneg (s-4*q^2)]
  rw [←mul_div_assoc]
  exact (le_div_iff₀ hs).mpr (by simpa using hsle)

section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem sparse_retained_pencil {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S S' : Finset (Projectivization K V)) (hS' : S'.Nonempty) (hsub : S'⊆S)
    (T : Finset (Projectivization K (Module.Dual K V))) (hsmall : S.card≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K)) :
    ((∑ i∈range (n+2),Nat.card K^i):ℝ)≤
      4*((Nat.card K:ℝ)^(n+2)/(S'.card:ℝ))^2 := by
  have hq : (2:ℝ)≤Nat.card K := by
    have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    exact_mod_cast hh
  have hs : (0:ℝ)<S'.card := by exact_mod_cast card_pos.mpr hS'
  have hh := sparse_smaller_square hdim S T hsmall hsparse
  have hsc : (S'.card:ℝ)≤S.card := by exact_mod_cast card_le_card hsub
  have hsq : (S'.card:ℝ)^2≤2*(Nat.card K:ℝ)^(n+2+1) := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hsc |>.trans hh
  simpa only [Nat.cast_sum,Nat.cast_pow] using
    scalar_pencil_card (Nat.card K) S'.card hq hs (n+2) (by omega) hsq
end
end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_EnumeratedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DescriptionEnumeration
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*}

lemma choose_exp_bound {N n : ℕ} (hn : 0<n) :
    (N.choose n:ℝ) ≤ exp (n*(log ((N:ℝ)/n)+1)) := by
  by_cases hN : N=0
  · subst N
    rw [Nat.choose_eq_zero_of_lt hn]
    simp only [Nat.cast_zero]
    exact (exp_pos _).le
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hN' : (0:ℝ)<N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hfact : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have he := Real.pow_div_factorial_le_exp (n:ℝ) (show (0:ℝ)≤n by positivity) n
  have hf : (1:ℝ)/n.factorial≤exp n/(n:ℝ)^n := by
    apply (div_le_div_iff₀ hfact (pow_pos hn' n)).mpr
    have hh := (div_le_iff₀ hfact).mp he
    simpa only [one_mul] using hh
  calc
    (N.choose n:ℝ) ≤ (N:ℝ)^n/n.factorial := Nat.choose_le_pow_div n N
    _ ≤ (N:ℝ)^n*(exp n/(n:ℝ)^n) := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hf (pow_nonneg hN'.le n)
    _ = exp n*((N:ℝ)/n)^n := by rw [div_pow]; ring
    _ = exp (n*(log ((N:ℝ)/n)+1)) := by
      rw [mul_add,mul_one,exp_add,exp_nat_mul,exp_log (div_pos hN' hn')]
      ring

theorem public_cover (U : Finset α) (n : ℕ) (hn : 0<n) (hnu : n≤U.card) :
    let caps := U.powersetCard n
    (∀ W∈caps,W⊆U ∧ W.card=n) ∧
    (∀ S,S⊆U → S.card=n → ∃ W∈caps,S∩W=S) ∧
    log ((caps.card:ℝ)+1)≤log 2+n*(log ((U.card:ℝ)/n)+1) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro W hW
    exact mem_powersetCard.mp hW
  · intro S hSU hSn
    exact ⟨S,mem_powersetCard.mpr ⟨hSU,hSn⟩,inter_self S⟩
  · rw [card_powersetCard]
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    have hnu' : (n:ℝ)≤U.card := by exact_mod_cast hnu
    have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr (by linarith))
    have hb : 0≤(n:ℝ)*(log ((U.card:ℝ)/n)+1) := by positivity
    have h := choose_exp_bound (N:=U.card) hn
    have he := one_le_exp_iff.mpr hb
    have hm : ((U.card.choose n:ℝ)+1)≤2*exp (n*(log ((U.card:ℝ)/n)+1)) := by linarith
    have hl := log_le_log (by positivity : (0:ℝ)<(U.card.choose n:ℝ)+1) hm
    rwa [log_mul (by norm_num) (exp_ne_zero _),log_exp] at hl

end
end SharpLogRamsey.DescriptionEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_GreedyIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

lemma residual_subset (S : Finset α) (U : β → Finset α) (bs : List β) :
    residual S U bs ⊆ S := by
  induction bs generalizing S with
  | nil => exact subset_rfl
  | cons b bs ih => exact (ih _).trans sdiff_subset

theorem card_partition (S : Finset α) (U : β → Finset α) (bs : List β) :
    ((cells S U bs).map Finset.card).sum + (residual S U bs).card = S.card := by
  induction bs generalizing S with
  | nil => simp [cells,residual]
  | cons b bs ih =>
    simp only [cells,residual,List.map_cons,List.sum_cons]
    have ht := ih (S \ U b)
    have he := card_sdiff_add_card_inter S (U b)
    omega

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

lemma residual_eq (S : Finset α) (U : β → Finset α) (bs : List β) :
    residual S U bs = S \ bs.toFinset.biUnion U := by
  induction bs generalizing S with
  | nil => simp [residual]
  | cons b bs ih =>
    rw [residual,ih]
    ext x
    simp only [mem_sdiff,List.toFinset_cons,mem_biUnion,mem_insert]
    aesop

lemma removed_subset (S : Finset α) (U : β → Finset α) (bs : List β) :
    removed S U bs ⊆ S := sdiff_subset

lemma removed_eq (S : Finset α) (U : β → Finset α) (bs : List β) :
    removed S U bs = S ∩ bs.toFinset.biUnion U := by
  rw [removed,residual_eq]
  ext x
  simp only [mem_sdiff,mem_inter]
  tauto

lemma removed_cons (S : Finset α) (U : β → Finset α) (b : β) (bs : List β) :
    removed S U (b::bs) = (S ∩ U b) ∪ removed (S \ U b) U bs := by
  simp only [removed_eq,List.toFinset_cons,biUnion_insert]
  ext x
  simp only [mem_union,mem_inter,mem_sdiff]
  tauto

lemma cell_subset_removed (S : Finset α) (U : β → Finset α) (bs : List β)
    (C : Finset α) (hC : C ∈ cells S U bs) : C ⊆ removed S U bs := by
  induction bs generalizing S with
  | nil => simp [cells] at hC
  | cons b bs ih =>
    rw [removed_cons]
    simp only [cells,List.mem_cons] at hC
    rcases hC with rfl | hc
    · exact subset_union_left
    · exact (ih _ hc).trans subset_union_right

lemma own_empty_or_cell (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x = ∅ ∨ own S U bs x ∈ cells S U bs := by
  induction bs generalizing S with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    rw [own]
    split_ifs with hx
    · exact Or.inr (by simp [cells])
    · rcases ih (S \ U b) with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by simp only [cells,List.mem_cons]; exact Or.inr hh)

lemma own_subset_removed (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x ⊆ removed S U bs := by
  rcases own_empty_or_cell S U bs x with hh | hh
  · rw [hh]; exact empty_subset _
  · exact cell_subset_removed S U bs _ hh

lemma removed_card (S : Finset α) (U : β → Finset α) (bs : List β) :
    (removed S U bs).card + (residual S U bs).card = S.card :=
  card_sdiff_add_card_eq_card (residual_subset S U bs)

lemma removed_card_eq_sum (S : Finset α) (U : β → Finset α) (bs : List β) :
    (removed S U bs).card = ((cells S U bs).map Finset.card).sum := by
  have h := removed_card S U bs
  have h' := card_partition S U bs
  omega

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

lemma cells_get (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : ℕ) (hi : i < bs.length) :
    (cells S U bs)[i]'(by rw [cells_length]; exact hi) =
      residual S U (bs.take i) ∩ U bs[i] := by
  induction bs generalizing S i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [cells,List.getElem_cons_succ,List.take_succ_cons,residual]
      exact ih (S \ U b) i (by simpa using hi)

lemma indexedCell_eq (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : Fin bs.length) : indexedCell S U bs i =
      (cells S U bs)[i.val]'(by rw [cells_length]; exact i.isLt) :=
  (cells_get S U bs i.val i.isLt).symm

lemma indexedCell_sum (S : Finset α) (U : β → Finset α) (bs : List β) :
    ∑ i : Fin bs.length, (indexedCell S U bs i).card = (removed S U bs).card := by
  rw [removed_card_eq_sum]
  induction bs generalizing S with
  | nil => simp [cells]
  | cons b bs ih =>
    change (∑ i : Fin (bs.length+1), (indexedCell S U (b::bs) i).card) = _
    rw [Fin.sum_univ_succ]
    simp only [indexedCell,Fin.val_zero,List.take_zero,residual,List.getElem_cons_zero,
      Fin.val_succ,List.take_succ_cons,List.getElem_cons_succ,cells,List.map_cons,List.sum_cons]
    congr 1
    exact ih (S \ U b)

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace SharpLogRamsey.ScaleSelection
open Filter Real
open scoped Topology
open SharpLogRamsey.MomentBudgetBridge

theorem eventually_polynomial_le_exp_rpow (C a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ Real.exp (c*x^b) := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound (show 0 < (1/(|C|+1) : ℝ) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    C*x^a ≤ (|C|+1)*x^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx0.le _)
    _ ≤ (|C|+1)*((1/(|C|+1))*Real.exp (c*x^b)) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by field_simp

theorem eventually_polynomial_exp_neg_rpow_lt (C a b c ε : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a*Real.exp (-c*x^b) < ε := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound
    (show 0 < ε/(2*(|C|+1)) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    _ ≤ (|C|+1)*x^a*Real.exp (-c*x^b) := by
      gcongr
    _ ≤ (|C|+1)*(ε/(2*(|C|+1))*Real.exp (c*x^b))*Real.exp (-c*x^b) := by
      gcongr
    _ = ε/2 := by
      rw [mul_assoc (|C|+1), mul_assoc, ← Real.exp_add,
        show c*x^b+-c*x^b=0 by ring, Real.exp_zero]
      field_simp
    _ < ε := by linarith

theorem certificate_le_majorant (x P : ℝ) (p D : ℕ) (hx : 1 ≤ x)
    (hP : 0 ≤ P) (hP' : P ≤ x^2) (hp : (p : ℝ) ≤ x^2) (hD : (D : ℝ) ≤ x^2) :
    certificateOverhead p D P ≤ majorant x := by
  have hA : anchorBudget p P ≤ 202*x^2 := by unfold anchorBudget; linarith
  have hA0 : 0 ≤ anchorBudget p P := anchorBudget_nonneg p hP
  unfold certificateOverhead majorant
  gcongr

theorem majorant_le (x : ℝ) (hx : 1 ≤ x) :
    majorant x ≤ (1+4+808+40804+5*2^200 : ℝ)*x^410 := by
  have hx0 : 0 ≤ x := by linarith
  have h0 : (1 : ℝ) ≤ x^410 := one_le_pow₀ hx
  have h4 : x^4 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have h8 : x^8 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have h12 : x^12 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have hD : x^2+4 ≤ 5*x^2 := by nlinarith [sq_nonneg (x-1)]
  have hm : (x^2)^4*(x^2+4)*(2*x^2)^200 ≤ 5*2^200*x^410 := by
    calc
      _ ≤ (x^2)^4*(5*x^2)*(2*x^2)^200 := by gcongr
      _ = _ := by ring
  have he : majorant x = 1+4*x^4+808*x^8+40804*x^12+
      (x^2)^4*(x^2+4)*(2*x^2)^200 := by unfold majorant; ring
  rw [he]
  nlinarith only [h0, h4, h8, h12, hm]

theorem eventually_certificate_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p D : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → (D : ℝ) ≤ x^2 → x^b ≤ P → P ≤ x^2 →
    certificateOverhead p D P ≤ Real.exp (2*P/25) := by
  have hh := eventually_polynomial_le_exp_rpow
    (1+4+808+40804+5*2^200) 410 b (2/25) hb (by norm_num)
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1 p D P hp hD hP hP'
  have hx0 : 0 ≤ x := by linarith
  calc
    _ ≤ majorant x := certificate_le_majorant x P p D hx1
      ((Real.rpow_nonneg hx0 _).trans hP) hP' hp hD
    _ ≤ (1+4+808+40804+5*2^200 : ℝ)*x^410 := majorant_le x hx1
    _ ≤ Real.exp ((2/25)*x^b) := by simpa only [Real.rpow_ofNat] using hx
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_shift_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p D : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → (D : ℝ) ≤ x^2 → x^b ≤ P →
    shiftOverhead p D ≤ Real.exp (2*P/25) := by
  have hh := eventually_polynomial_le_exp_rpow (4+200^200) 402 b (2/25) hb (by norm_num)
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1 p D P hp hD hP
  have hx0 : 0 ≤ x := by linarith
  have hm : shiftOverhead p D ≤ (4+200^200 : ℝ)*x^402 := by
    have h0 : (1 : ℝ) ≤ x^402 := one_le_pow₀ hx1
    have hh : (D : ℝ)*(200*(p : ℝ))^200 ≤ 200^200*x^402 := by
      calc
        _ ≤ x^2*(200*x^2)^200 := mul_le_mul hD
          (pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left hp (by norm_num)) 200)
          (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg p)) 200) (sq_nonneg x)
        _ = _ := by ring
    unfold shiftOverhead
    nlinarith only [h0, hh]
  calc
    _ ≤ (4+200^200 : ℝ)*x^402 := hm
    _ ≤ Real.exp ((2/25)*x^b) := by simpa only [Real.rpow_ofNat] using hx
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_position_budgets (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → x^b ≤ P →
    (p : ℝ)^2 ≤ Real.exp (P/10) ∧ 2*(p : ℝ)+3 ≤ Real.exp (P/10) := by
  have hh := eventually_polynomial_le_exp_rpow 1 4 b (1/10) hb (by norm_num)
  have hh' := eventually_polynomial_le_exp_rpow 5 2 b (1/10) hb (by norm_num)
  filter_upwards [hh, hh', eventually_ge_atTop (1 : ℝ)] with x hx hx' hx1 p P hp hP
  have hx0 : 0 ≤ x := by linarith
  have he : Real.exp ((1/10)*x^b) ≤ Real.exp (P/10) := Real.exp_le_exp.mpr (by linarith)
  constructor
  · calc
      _ ≤ (x^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hp _
      _ = x^4 := by ring
      _ ≤ Real.exp ((1/10)*x^b) := by simpa only [one_mul, Real.rpow_ofNat] using hx
      _ ≤ _ := he
  · have h1 : 1 ≤ x^2 := one_le_pow₀ hx1
    calc
      _ ≤ 5*x^2 := by linarith
      _ ≤ Real.exp ((1/10)*x^b) := by simpa only [Real.rpow_ofNat] using hx'
      _ ≤ _ := he

lemma nineteen_twentieth_pow_le (n : ℕ) :
    (19/20 : ℝ)^n ≤ Real.exp (-(n : ℝ)/20) := by
  have hb : (19/20 : ℝ) ≤ Real.exp (-(1/20 : ℝ)) := by
    linarith only [Real.add_one_le_exp (-(1/20 : ℝ))]
  calc
    _ ≤ (Real.exp (-(1/20 : ℝ)))^n := pow_le_pow_left₀ (by norm_num) hb _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem eventually_root_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p R : ℕ), (p : ℝ) ≤ x^2 → x^b ≤ R →
    ∃ h : ℕ, 0 < h ∧ 400 ≤ R ∧ h ≤ (R/2)/400 ∧
      (p : ℝ)*h*(19/20 : ℝ)^(h-1) < 1/2 := by
  have hh := eventually_polynomial_exp_neg_rpow_lt (Real.exp (1/10)) (2+b) b
    (1/16000) (1/2) hb (by norm_num) (by norm_num)
  filter_upwards [hh, (tendsto_rpow_atTop hb).eventually_ge_atTop 1600,
    eventually_ge_atTop (1 : ℝ)] with x hx hxb hx1 p R hp hR
  have hx0 : 0 < x := by linarith
  let h : ℕ := ⌊x^b/800⌋₊
  have hh1 : 1 ≤ h := by
    apply Nat.le_floor
    norm_num
    linarith
  have hhle : (h : ℝ) ≤ x^b/800 := Nat.floor_le (by positivity)
  have hhgt : x^b/800 < (h : ℝ)+1 := Nat.lt_floor_add_one _
  have hhr : 800*h ≤ R := by
    have hcast : (800 : ℝ)*(h : ℝ) ≤ R := by linarith
    exact_mod_cast hcast
  have hnat : ((h-1 : ℕ) : ℝ) = (h : ℝ)-1 := by rw [Nat.cast_sub hh1]; norm_num
  have hp' : (p : ℝ)*h ≤ x^(2+b) := by
    calc
      _ ≤ x^2*x^b := by gcongr; linarith only [hhle, Real.rpow_nonneg hx0.le b]
      _ = _ := by rw [Real.rpow_add hx0]; simp only [Real.rpow_ofNat]
  have he : (19/20 : ℝ)^(h-1) ≤ Real.exp ((1/10)-(1/16000)*x^b) := by
    apply (nineteen_twentieth_pow_le (h-1)).trans
    apply Real.exp_le_exp.mpr
    rw [hnat]
    linarith
  refine ⟨h, by omega, by omega, by omega, ?_⟩
  calc
    _ ≤ x^(2+b)*Real.exp ((1/10)-(1/16000)*x^b) :=
      mul_le_mul hp' he (by positivity) (by positivity)
    _ = Real.exp (1/10)*x^(2+b)*Real.exp (-(1/16000)*x^b) := by
      rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      ring
    _ < _ := hx

end SharpLogRamsey.ScaleSelection
end

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection SharpLogRamsey.MomentBudgetBridge

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

lemma exponent_gap {η : ℝ} (hη : 0 < η) : 1-η/2+9*beta η < 1 := by
  unfold beta
  linarith

lemma scale_bounds {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0 < η)
    (h : Admissible σ η D R) :
    σ^(9*beta η) ≤ scaleL σ η D ∧
    σ^(10*beta η) ≤ scaleP σ η D R ∧
    scaleP σ η D R ≤ 4*σ^(1-η/2+9*beta η) := by
  have hσ0 : 0 < σ := by linarith
  have hb : 0 < beta η := beta_pos hη
  have hpow : 1 ≤ σ^beta η := Real.one_le_rpow hσ hb.le
  have hD0 : 0 ≤ D := (Real.rpow_nonneg hσ0.le _).trans h.D_lower
  have hL : σ^(9*beta η) ≤ scaleL σ η D := by
    calc
      _ = σ^beta η*σ^(8*beta η) := by rw [← Real.rpow_add hσ0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.D_lower (Real.rpow_nonneg hσ0.le _)
  refine ⟨hL, ?_, ?_⟩
  · calc
      _ = σ^(9*beta η)*σ^beta η := by rw [← Real.rpow_add hσ0]; congr 1; ring
      _ ≤ scaleL σ η D*(R : ℝ) := mul_le_mul hL h.R_lower
        (Real.rpow_nonneg hσ0.le _) (by unfold scaleL; positivity)
      _ = _ := rfl
  · have hR : (R : ℝ) ≤ 4*σ^beta η := by linarith [h.R_upper]
    calc
      _ ≤ (σ^(1-η/2)*σ^(8*beta η))*(4*σ^beta η) := by
        unfold scaleP scaleL
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.D_upper
          (Real.rpow_nonneg hσ0.le _)) hR (Nat.cast_nonneg _) (by positivity)
      _ = 4*σ^(1-η/2+9*beta η) := by
        rw [mul_assoc, mul_left_comm (σ^(8*beta η)) 4, ← mul_assoc,
          mul_comm (σ^(1-η/2)) 4, mul_assoc, ← Real.rpow_add hσ0,
          ← Real.rpow_add hσ0]
        congr 2
        ring

lemma eventually_monomial_le_linear (C a ε : ℝ) (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-1))*x := by
      have hp : x^(a-1)*x = x^a := by
        calc
          _ = x^(a-1)*x^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
      rw [mul_assoc, hp]
    _ ≤ ε*x := mul_le_mul_of_nonneg_right hx.le hx0.le

theorem eventually_P_le_linear {η : ℝ} (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      scaleP σ η D R ≤ ε*σ := by
  filter_upwards [eventually_monomial_le_linear 4 (1-η/2+9*beta η) ε
    (exponent_gap hη) hε, eventually_ge_atTop (1 : ℝ)] with σ hσ hσ1 D R h
  exact (scale_bounds hσ1 hη h).2.2.trans hσ

theorem moment_order_le {σ P : ℝ} {p : ℕ} (hσ : 10002 ≤ σ) (hP : 1 ≤ P)
    (hp : (p : ℝ) ≤ 10000*σ/P+2) : (p : ℝ) ≤ σ^2 := by
  have hσ0 : 0 ≤ σ := by linarith
  have hdiv : 10000*σ/P ≤ 10000*σ := div_le_self (by positivity) hP
  nlinarith [sq_nonneg (σ-10002)]

theorem eventually_enumeration_budgets {η : ℝ} (hη : 0 < η) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R p m : ℕ), Admissible σ η D R →
    (p : ℝ) ≤ 10000*σ/scaleP σ η D R+2 → (m : ℝ) ≤ σ^2 →
    10000 ≤ scaleL σ η D ∧
    certificateOverhead p m (scaleP σ η D R) ≤ Real.exp (2*scaleP σ η D R/25) ∧
    shiftOverhead p m ≤ Real.exp (2*scaleP σ η D R/25) ∧
    (p : ℝ)^2 ≤ Real.exp (scaleP σ η D R/10) ∧
    2*(p : ℝ)+3 ≤ Real.exp (scaleP σ η D R/10) ∧
    ∃ h : ℕ, 0 < h ∧ 400 ≤ R ∧ h ≤ (R/2)/400 ∧
      (p : ℝ)*h*(19/20 : ℝ)^(h-1) < 1/2 := by
  have hb := beta_pos hη
  have h10 : 0 < 10*beta η := by positivity
  have h9 : 0 < 9*beta η := by positivity
  filter_upwards [eventually_certificate_budget (10*beta η) h10,
    eventually_shift_budget (10*beta η) h10,
    eventually_position_budgets (10*beta η) h10,
    eventually_root_budget (beta η) hb,
    (tendsto_rpow_atTop h9).eventually_ge_atTop 10000,
    eventually_P_le_linear hη 1 (by norm_num),
    eventually_ge_atTop (10002 : ℝ)] with σ hc hs hp hr hL hPu hσ D R p m had hp' hm
  have hσ1 : 1 ≤ σ := by linarith
  obtain ⟨hLb, hPb, _⟩ := scale_bounds hσ1 hη had
  have hP1 : 1 ≤ scaleP σ η D R := (Real.one_le_rpow hσ1 h10.le).trans hPb
  have hpm : (p : ℝ) ≤ σ^2 := moment_order_le hσ hP1 hp'
  have hP2 : scaleP σ η D R ≤ σ^2 := by
    have := hPu D R had
    nlinarith [sq_nonneg (σ-1)]
  obtain ⟨hp2, hps⟩ := hp p (scaleP σ η D R) hpm hPb
  exact ⟨hL.trans hLb, hc p m _ hpm hm hPb hP2,
    hs p m _ hpm hm hPb, hp2, hps, hr p R hpm had.R_lower⟩

end SharpLogRamsey.SourceScales
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScaleComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

lemma Kstar_eq (σ η D : ℝ) (hσ : 0<σ) :
    scaleKstar σ η D=scaleL σ η D*σ^(-2*beta η) := by
  unfold scaleKstar scaleL
  rw [mul_assoc,←Real.rpow_add hσ]
  congr 2
  ring

lemma R_bound {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0<η)
    (h : Admissible σ η D R) : (R:ℝ) ≤ 4*σ^beta η := by
  have hh := Real.one_le_rpow hσ (beta_pos hη).le
  linarith [h.R_upper]

lemma L_pos {σ η D : ℝ} {R : ℕ} (hσ : 0<σ) (h : Admissible σ η D R) :
    0 < scaleL σ η D := by
  have hD : 0<D := (Real.rpow_pos_of_pos hσ _).trans_le h.D_lower
  unfold scaleL
  positivity

lemma P_pos {σ η D : ℝ} {R : ℕ} (hσ : 0<σ) (h : Admissible σ η D R) :
    0 < scaleP σ η D R := by
  have hR : (0:ℝ)<R := (Real.rpow_pos_of_pos hσ _).trans_le h.R_lower
  exact mul_pos (L_pos hσ h) hR

theorem eventually_sparse_loss {η : ℝ} (hη : 0<η) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      ∀ b τ : ℝ, b ≤ C*scaleKstar σ η D → τ ≤ C*σ^(-100*beta η) →
      b+scaleP σ η D R*τ ≤ δ*scaleL σ η D := by
  have hb := beta_pos hη
  have h1 : Tendsto (fun σ : ℝ => C*σ^(-2*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<2*beta η by positivity)).const_mul C using 1 <;> simp [neg_mul]
  have h2 : Tendsto (fun σ : ℝ => 4*C*σ^(-99*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<99*beta η by positivity)).const_mul (4*C) using 1 <;> simp [neg_mul]
  have ht : Tendsto (fun σ : ℝ => C*σ^(-2*beta η)+4*C*σ^(-99*beta η)) atTop (𝓝 0) := by
    simpa using h1.add h2
  filter_upwards [ht.eventually (gt_mem_nhds hδ),eventually_ge_atTop (1:ℝ)] with σ he hσ D R had b τ hb' hτ
  have hσ0 : 0<σ := by linarith
  have hL := (L_pos hσ0 had).le
  have hP := (P_pos hσ0 had).le
  have hR := R_bound hσ hη had
  have hh : (R:ℝ)*(C*σ^(-100*beta η)) ≤ 4*C*σ^(-99*beta η) := by
    calc
      _  ≤  (4*σ^beta η)*(C*σ^(-100*beta η)) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
      _ = _ := by
        rw [show (4*σ^beta η)*(C*σ^(-100*beta η))=4*C*(σ^beta η*σ^(-100*beta η)) by ring,
          ←Real.rpow_add hσ0]
        congr 2
        ring
  have hb'' : b ≤ scaleL σ η D*(C*σ^(-2*beta η)) := by
    rw [Kstar_eq σ η D hσ0] at hb'
    nlinarith only [hb']
  have hτ' : scaleP σ η D R*τ ≤ scaleL σ η D*(4*C*σ^(-99*beta η)) := by
    calc
      _  ≤  scaleP σ η D R*(C*σ^(-100*beta η)) := mul_le_mul_of_nonneg_left hτ hP
      _ = scaleL σ η D*((R:ℝ)*(C*σ^(-100*beta η))) := mul_assoc _ _ _
      _  ≤  _ := mul_le_mul_of_nonneg_left hh hL
  calc
    _  ≤  scaleL σ η D*(C*σ^(-2*beta η)+4*C*σ^(-99*beta η)) := by linarith
    _  ≤  scaleL σ η D*δ := mul_le_mul_of_nonneg_left he.le hL
    _ = _ := mul_comm _ _

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourcePencilScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

lemma eventually_uniform_L {η : ℝ} (hη : 0<η) {Q : ℝ→Prop}
    (hQ : ∀ᶠ L : ℝ in atTop,Q L) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R → Q (scaleL σ η D) := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp hQ
  have ht := (tendsto_rpow_atTop (show 0<9*beta η by have := beta_pos hη; positivity)).eventually
    (eventually_ge_atTop a)
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with σ hσ hσ1 D R had
  exact ha _ (hσ.trans (scale_bounds hσ1 hη had).1)

lemma eventually_uniform_R {η : ℝ} (hη : 0<η) (a : ℝ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R → a≤(R:ℝ) := by
  have ht := (tendsto_rpow_atTop (beta_pos hη)).eventually (eventually_ge_atTop a)
  filter_upwards [ht] with σ hσ D R had
  exact hσ.trans had.R_lower

lemma two_pow_le_exp (R : ℕ) : (2:ℝ)^R≤Real.exp (R:ℝ) := by
  have ht : (2:ℝ)≤Real.exp 1 := by
    have hh := Real.add_one_le_exp (1:ℝ)
    norm_num at hh ⊢
    exact hh
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) ht R
  simpa only [←Real.exp_nat_mul,mul_one] using hh

theorem eventually_pencil_scalar_budgets {η : ℝ} (hη : 0<η) (C : ℝ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R N : ℕ),Admissible σ η D R → (N:ℝ)≤σ^2 →
      let L := scaleL σ η D
      let P := scaleP σ η D R
      C*2^R≤Real.exp (P/20) ∧
      (2*L^2)^R≤Real.exp (P/25) ∧
      C^2*Real.exp (L/50)+(N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/20) ∧
      2≤Real.exp (P/20) ∧
      400000*Real.exp (L/1000)≤Real.exp (P/100) := by
  have hconst : ∀ᶠ L : ℝ in atTop,C≤Real.exp (L/1000) ∧ C^2≤Real.exp (L/1000) := by
    have ht : Tendsto (fun L : ℝ => Real.exp (L/1000)) atTop atTop :=
      tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<1000))
    exact (ht.eventually (eventually_ge_atTop C)).and (ht.eventually (eventually_ge_atTop (C^2)))
  have hpoly : ∀ᶠ L : ℝ in atTop,2*L^2≤Real.exp (L/25) := by
    have hh := ScaleSelection.eventually_polynomial_le_exp_rpow 2 2 1 (1/25)
      (by norm_num) (by norm_num)
    simpa only [Real.rpow_one,Real.rpow_ofNat,div_eq_mul_inv,mul_comm,one_mul] using hh
  have hgrid := ScaleSelection.eventually_polynomial_le_exp_rpow 1 2 (9*beta η) (1/1000)
    (by have := beta_pos hη; positivity) (by norm_num)
  have hlarge : ∀ᶠ L : ℝ in atTop,1000000000≤L := eventually_ge_atTop _
  filter_upwards [eventually_uniform_L hη hconst,eventually_uniform_L hη hpoly,
    eventually_uniform_L hη hlarge,eventually_uniform_R hη 400,hgrid,
    eventually_ge_atTop (1:ℝ)] with σ hc hp hl hr hg hσ D R N had hN
  let L := scaleL σ η D
  let P := scaleP σ η D R
  have hL : 1000000000≤L := hl D R had
  have hR : (400:ℝ)≤R := hr D R had
  have hL0 : 0≤L := by linarith
  have hR1 : (1:ℝ)≤R := by linarith
  have hP : P=L*R := rfl
  have hPL : 400*L≤P := by rw [hP]; nlinarith
  have hPR : 1000000000*(R:ℝ)≤P := by rw [hP]; nlinarith
  have hP0 : 0≤P := by linarith
  have hcc := hc D R had
  change C≤Real.exp (L/1000) ∧ C^2≤Real.exp (L/1000) at hcc
  have hNN : (N:ℝ)≤Real.exp (L/1000) := by
    apply hN.trans
    calc
      σ^2≤Real.exp ((1/1000)*σ^(9*beta η)) := by simpa only [one_mul,Real.rpow_ofNat] using hg
      _ ≤ Real.exp (L/1000) := Real.exp_le_exp.mpr (by linarith [(scale_bounds hσ hη had).1])
  have ht := two_pow_le_exp R
  have h2 : (2:ℝ)≤Real.exp (P/40) := by
    have hh := Real.add_one_le_exp (P/40)
    linarith
  dsimp only
  change C*2^R≤Real.exp (P/20) ∧ (2*L^2)^R≤Real.exp (P/25) ∧
    C^2*Real.exp (L/50)+(N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/20) ∧
    2≤Real.exp (P/20) ∧ 400000*Real.exp (L/1000)≤Real.exp (P/100)
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      C*2^R≤Real.exp (L/1000)*Real.exp (R:ℝ) := mul_le_mul hcc.1 ht (by positivity) (Real.exp_pos _).le
      _ = Real.exp (L/1000+R) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (P/20) := Real.exp_le_exp.mpr (by linarith)
  · have hh := pow_le_pow_left₀ (show 0≤2*L^2 by positivity) (hp D R had) R
    apply hh.trans_eq
    rw [←Real.exp_nat_mul]
    congr 1
    rw [hP]
    ring
  · have hfirst : C^2*Real.exp (L/50)≤Real.exp (P/40) := by
      calc
        _ ≤ Real.exp (L/1000)*Real.exp (L/50) := mul_le_mul_of_nonneg_right hcc.2 (Real.exp_pos _).le
        _ = Real.exp (L/1000+L/50) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have hsecond : (N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/40) := by
      calc
        _ ≤ (Real.exp (L/1000)*Real.exp (R:ℝ))*Real.exp (P/50) := by gcongr
        _ = Real.exp (L/1000+R+P/50) := by rw [←Real.exp_add,←Real.exp_add]
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ 2*Real.exp (P/40) := by linarith
      _ ≤ Real.exp (P/40)*Real.exp (P/40) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (P/20) := by rw [←Real.exp_add]; congr 1; ring
  · exact h2.trans (Real.exp_le_exp.mpr (by linarith))
  · have hnum : (400000:ℝ)≤Real.exp (L/1000) := by
      have hh := Real.add_one_le_exp (L/1000)
      linarith
    calc
      _ ≤ Real.exp (L/1000)*Real.exp (L/1000) := mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le
      _ = Real.exp (L/500) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceTrainingScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_training_loss {η : ℝ} (hη : 0<η) (C δ : ℝ)
    (hC : 0≤C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∀ b τ : ℝ,b≤C*scaleKstar σ η D → τ≤C*σ^(-100*beta η) →
        b+2*scaleP σ η D R*τ≤δ*scaleL σ η D := by
  filter_upwards [eventually_sparse_loss hη (2*C) δ (by positivity) hδ,
    eventually_ge_atTop (1:ℝ)] with σ hh hσ D R had b τ hb hτ
  have hK : 0 ≤ scaleKstar σ η D := by
    rw [Kstar_eq _ _ _ (by linarith)]
    exact mul_nonneg (L_pos (by linarith) had).le (Real.rpow_nonneg (by linarith) _)
  have h1 : b≤(2*C)*scaleKstar σ η D := by nlinarith
  have h2 : 2*τ≤(2*C)*σ^(-100*beta η) := by linarith
  have hh' := hh D R had b (2*τ) h1 h2
  nlinarith only [hh']

theorem eventually_exceptional_training {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∀ b τ : ℝ,b≤C*scaleKstar σ η D → τ≤C*σ^(-100*beta η) →
        50000*Real.exp (-(95/100:ℝ)*scaleL σ η D)≤
          Real.exp (-b-2*scaleP σ η D R*τ)/800 := by
  have he : ∀ᶠ L : ℝ in atTop,(40000000:ℝ)≤Real.exp (L/2) := by
    filter_upwards [eventually_ge_atTop (80000000:ℝ)] with L hL
    have hh := Real.add_one_le_exp (L/2)
    linarith
  filter_upwards [eventually_training_loss hη C (1/100) hC (by norm_num),
    eventually_uniform_L hη he,eventually_ge_atTop (1:ℝ)] with σ hl he hσ D R had b τ hb hτ
  have hL := (L_pos (by linarith) had).le
  have hl' := hl D R had b τ hb hτ
  have he' := he D R had
  have hh : 40000000*Real.exp (-(95/100:ℝ)*scaleL σ η D)≤
      Real.exp (-b-2*scaleP σ η D R*τ) := by
    calc
      _ ≤ Real.exp (scaleL σ η D/2)*Real.exp (-(95/100:ℝ)*scaleL σ η D) :=
        mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
      _ = Real.exp (scaleL σ η D/2-(95/100:ℝ)*scaleL σ η D) := by
        rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_LearningScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.LearningScalar
open Real
noncomputable section

lemma power_ratio_bound {B t P c : ℝ} (p : ℕ) (hB : 0≤B) (ht : 0<t)
    (hr : B/t≤exp (P/100)) :
    B^p*exp (-c*((p:ℝ)*P))/t^p≤exp ((p:ℝ)*(P/100-c*P)) := by
  calc
    _ = (B/t)^p*exp (-c*((p:ℝ)*P)) := by rw [div_pow]; ring
    _ ≤ (exp (P/100))^p*exp (-c*((p:ℝ)*P)) := by gcongr
    _ = _ := by rw [←exp_nat_mul,←exp_add]; congr 1; ring

theorem short_row_lower {σ P B N Q W b e : ℝ} {p : ℕ}
    (_hσ : 1≤σ) (hP : 100000000000000≤P) (hPu : P≤σ)
    (hB : 0<B) (hN : 1≤N) (hQ : 0≤Q) (hQu : Q≤2*exp (3*σ))
    (_hW : 0≤W) (hWu : W≤20804*exp σ*B)
    (hb : 0≤b) (_he : 0≤e) (hloss : b+e≤P/1000000)
    (hp : 10000*σ≤(p:ℝ)*P) :
    let z := exp σ*B*exp (-b-e)/8
    let t := z/(10*exp σ)
    let εs := B^2*exp (-(3/5:ℝ)*P)/t^2
    let εa := B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p
    exp (-e)/4≤exp (-e)/2-W*exp (-P/1000)/((1/1000:ℝ)*z)-
      N*εs/(N/100)-Q*εa/N-2*exp (-(exp σ*P)/3) := by
  let z := exp σ*B*exp (-b-e)/8
  let t := z/(10*exp σ)
  have hN0 : 0<N := by linarith
  have hP0 : 0≤P := by linarith
  have hz : 0<z := by dsimp [z]; positivity
  have ht : 0<t := by dsimp [t]; positivity
  have heP : e≤P := by linarith
  have ha : 80≤exp (P/200) := by have hh := add_one_le_exp (P/200); linarith
  have ha' : 80*exp (b+e)≤exp (P/100) := by
    calc
      _ ≤ exp (P/200)*exp (b+e) := mul_le_mul_of_nonneg_right ha (exp_pos _).le
      _ = _ := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hr : B/t≤exp (P/100) := by
    have hh : B/t=80*exp (b+e) := by
      dsimp [t,z]
      have hx : exp (-b-e)*exp (b+e)=1 := by rw [←exp_add]; ring_nf; exact exp_zero
      field_simp
      nlinarith only [hx]
    rw [hh]
    exact ha'
  have hεs : B^2*exp (-(3/5:ℝ)*P)/t^2≤exp (-29*P/50) := by
    have hh := power_ratio_bound 2 hB.le ht hr (c:=3/10)
    norm_num only [Nat.cast_ofNat] at hh
    rw [show -(3/10:ℝ)*(2*P)=-(3/5:ℝ)*P by ring,
      show (2:ℝ)*(P/100-3/10*P)=-29*P/50 by ring] at hh
    exact hh
  have hεa : B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p≤exp (-9*(p:ℝ)*P/100) := by
    have hh := power_ratio_bound p hB.le ht hr (c:=1/10)
    rw [show (p:ℝ)*(P/100-1/10*P)=-9*(p:ℝ)*P/100 by ring] at hh
    exact hh
  have hwerr : W*exp (-P/1000)/((1/1000:ℝ)*z)≤exp (-e)/16 := by
    have hc : 2662912000≤exp (P/2000) := by
      have hh := add_one_le_exp (P/2000)
      linarith
    have hh : 166432000*exp (b+e-P/1000)≤exp (-e)/16 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
      calc
        _ = 2662912000*exp (b+e-P/1000) := by ring
        _ ≤ exp (P/2000)*exp (b+e-P/1000) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
        _ = _ := (exp_add _ _).symm
        _ ≤ _ := exp_le_exp.mpr (by linarith)
    apply le_trans _ hh
    have hh' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hWu (exp_pos (-P/1000)).le)
      (show 0≤(1/1000:ℝ)*z by positivity)
    apply hh'.trans_eq
    dsimp [z]
    have hx : exp (-P/1000)=exp (b+e-P/1000)*exp (-b-e) := by
      rw [←exp_add]; congr 1; ring
    rw [hx]
    field_simp
    ring
  have hserr : N*(B^2*exp (-(3/5:ℝ)*P)/t^2)/(N/100)≤exp (-e)/16 := by
    have hc : 1600≤exp (P/2) := by have hh := add_one_le_exp (P/2); linarith
    calc
      _ = 100*(B^2*exp (-(3/5:ℝ)*P)/t^2) := by field_simp
      _ ≤ 100*exp (-29*P/50) := mul_le_mul_of_nonneg_left hεs (by norm_num)
      _ ≤ exp (-e)/16 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
        calc
          _ = 1600*exp (-29*P/50) := by ring
          _ ≤ exp (P/2)*exp (-29*P/50) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
          _ = _ := (exp_add _ _).symm
          _ ≤ _ := exp_le_exp.mpr (by linarith)
  have haerr : Q*(B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p)/N≤exp (-e)/16 := by
    have hc : 32≤exp (896*σ) := by have hh := add_one_le_exp (896*σ); linarith
    calc
      _ ≤ Q*exp (-9*(p:ℝ)*P/100)/N := by gcongr
      _ ≤ (2*exp (3*σ))*exp (-900*σ) := by
        have hex : exp (-9*(p:ℝ)*P/100)≤exp (-900*σ) := exp_le_exp.mpr (by linarith only [hp])
        calc
          _ ≤ Q*exp (-9*(p:ℝ)*P/100) := div_le_self (by positivity) hN
          _ ≤ _ := mul_le_mul hQu hex (exp_pos _).le (by positivity)
      _ = 2*exp (-897*σ) := by rw [mul_assoc,←exp_add]; congr 2; ring
      _ ≤ exp (-e)/16 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
        calc
          _ = 32*exp (-897*σ) := by ring
          _ ≤ exp (896*σ)*exp (-897*σ) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
          _ = exp (-σ) := by rw [←exp_add]; congr 1; ring
          _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hcut : 2*exp (-(exp σ*P)/3)≤exp (-e)/16 := by
    have hc : 32≤exp (P/4) := by have hh := add_one_le_exp (P/4); linarith
    have hq : 1≤exp σ := one_le_exp_iff.mpr (by linarith)
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
    calc
      _ = 32*exp (-(exp σ*P)/3) := by ring
      _ ≤ exp (P/4)*exp (-(exp σ*P)/3) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
      _ = _ := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hq hP0])
  dsimp only
  change exp (-e)/4≤exp (-e)/2-W*exp (-P/1000)/((1/1000:ℝ)*z)-
    N*(B^2*exp (-(3/5:ℝ)*P)/t^2)/(N/100)-
    Q*(B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p)/N-2*exp (-(exp σ*P)/3)
  linarith only [hwerr,hserr,haerr,hcut]

lemma row_capture {N X P : ℝ} (hN : 0≤N) (hP : 100000≤P)
    (hX : X≤N*exp (-P/200)+N/10000) :
    N/2≤N-X-N/100-(10*((1/1000:ℝ)+1/1000))*N := by
  have he : 100≤exp (P/200) := by
    have hh := add_one_le_exp (P/200)
    linarith
  have he' : exp (-P/200)≤1/100 := by
    rw [show -P/200=-(P/200) by ring,exp_neg]
    exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by simpa using he)
  have hh := mul_le_mul_of_nonneg_left he' hN
  linarith

lemma row_size {N q P D b e : ℝ} (hN : 0<N) (hq : 0<q)
    (hP : 100000≤P) (hloss : b+e≤P) (hsmall : 2*q*P≤N)
    (hD : D≤2*N+N*exp (5*P)) (j : ℕ) :
    2*q*P+D+N+100*q^(j+1)/(q*(q^j/N)*exp (-b-e)/8)≤N*exp (6*P) := by
  have hqB : 100*q^(j+1)/(q*(q^j/N)*exp (-b-e)/8)=800*N*exp (b+e) := by
    rw [pow_succ]
    have hx : exp (-b-e)*exp (b+e)=1 := by
      rw [←exp_add,show -b-e+(b+e)=0 by ring,exp_zero]
    field_simp
    nlinarith only [hx]
  rw [hqB]
  have he : 804≤exp P := by have hh := add_one_le_exp P; linarith
  have h1 : 1≤exp (5*P) := one_le_exp_iff.mpr (by linarith)
  have hbe : exp (b+e)≤exp (5*P) := exp_le_exp.mpr (by linarith)
  calc
    _ ≤ N*(4+exp (5*P)+800*exp (b+e)) := by linarith only [hsmall,hD]
    _ ≤ 804*N*exp (5*P)+N*exp (5*P) := by nlinarith
    _ ≤ N*exp (6*P) := by
      have he' : 805≤exp P := by have hh := add_one_le_exp P; linarith
      calc
        _ = N*(805*exp (5*P)) := by ring
        _ ≤ N*(exp P*exp (5*P)) := by gcongr
        _ = _ := by rw [←exp_add]; congr 2; ring

end
end SharpLogRamsey.LearningScalar

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PoissonSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PoissonSupport
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma sum_extend (S : Finset ι) (ω : S → ℕ) :
    (∑ i,extend S ω i)=∑ i : S,ω i := by
  classical
  rw [←sum_subset (subset_univ S) (fun i _ hi => by simp [extend,hi])]
  rw [←sum_coe_sort]
  apply sum_congr rfl
  intro i _
  simp [extend,i.2]

end
end SharpLogRamsey.PoissonSupport

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningRowBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace SharpLogRamsey.PoissonTail
open MeasureTheory ProbabilityTheory Finset
open SharpLogRamsey.BoundedProbability SharpLogRamsey.PoissonGrouping
open scoped BigOperators NNReal Classical
noncomputable section

lemma weighted_power_hasSum (r : ℝ≥0) (a : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ))*(r:ℝ)^n/(n.factorial:ℝ)*a^n)
      (Real.exp ((r:ℝ)*(a-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r:ℝ)*a)).mul_left (Real.exp (-(r:ℝ)))
  convert! h using 1
  · funext n
    rw [mul_pow]
    ring
  · rw [←Real.exp_eq_exp_ℝ,←Real.exp_add]
    congr 1
    ring

lemma integrable_power (r : ℝ≥0) (a : ℝ) :
    Integrable (fun n : ℕ => a^n) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs,abs_pow] using (weighted_power_hasSum r |a|).summable

lemma integral_power (r : ℝ≥0) (a : ℝ) :
    (∫ n : ℕ,a^n ∂poissonMeasure r)=Real.exp ((r:ℝ)*(a-1)) := by
  rw [integral_poissonMeasure' (integrable_power r a)]
  simpa only [smul_eq_mul] using (weighted_power_hasSum r a).tsum_eq

theorem double_mean_tail (r : ℝ≥0) :
    (poissonMeasure r).real {n : ℕ | 2*(r:ℝ)≤n} ≤ Real.exp (-(r:ℝ)/3) := by
  have hlog : 2/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hE : {n : ℕ | 2*(r:ℝ)≤n} ⊆
      {n : ℕ | Real.exp (2*(r:ℝ)*Real.log 2) ≤ (2:ℝ)^n} := by
    intro n hn
    change Real.exp (2*(r:ℝ)*Real.log 2) ≤ (2:ℝ)^n
    have he : (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [he]
    change 2*(r:ℝ)≤(n:ℝ) at hn
    apply Real.exp_le_exp.mpr
    nlinarith
  have hm := real_markov (poissonMeasure r) (fun n : ℕ => (2:ℝ)^n)
    (integrable_power r 2) (fun _ => by positivity)
    (Real.exp (2*(r:ℝ)*Real.log 2)) (Real.exp_pos _).le
    (Set.to_countable _).measurableSet
  rw [integral_power] at hm
  have ht : (poissonMeasure r).real {n : ℕ | Real.exp (2*(r:ℝ)*Real.log 2)≤(2:ℝ)^n} ≤
      Real.exp ((r:ℝ)-2*(r:ℝ)*Real.log 2) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [sub_self, sub_zero,show (2:ℝ)-1=1 by norm_num,mul_one,mul_comm] using hm
  apply (measureReal_mono (h₂:=measure_ne_top _ _) hE).trans (ht.trans ?_)
  apply Real.exp_le_exp.mpr
  nlinarith [r.coe_nonneg]

theorem total_tail {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) :
    (law rate).real {ω | 2*(∑ i,(rate i:ℝ)) ≤ (∑ i,ω i : ℕ)} ≤
      Real.exp (-(∑ i,(rate i:ℝ))/3) := by
  have h := sum_hasLaw rate univ
  have hm := h.measurePreserving (measurable_of_countable _)
  have he : (law rate).real {ω | 2*(∑ i,(rate i:ℝ)) ≤ (∑ i,ω i : ℕ)} =
      (poissonMeasure (∑ i,rate i)).real {n : ℕ | 2*(∑ i,(rate i:ℝ))≤n} := by
    unfold Measure.real
    rw [←hm.measure_preimage (Set.to_countable _).measurableSet.nullMeasurableSet]
    rfl
  rw [he]
  simpa using double_mean_tail (∑ i,rate i)

end
end SharpLogRamsey.PoissonTail

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PointScore
open scoped BigOperators Classical
noncomputable section
variable {A H : Type*} [Fintype A] [Fintype H]

omit [Fintype A] [Fintype H] in
lemma score_eq (S O : Finset A) (T : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) :
    score S O T inc b ω = ∑ h∈T, ∏ r,
      pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
        (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b) := by
  exact sum_coe_sort T (fun h : H => ∏ r,
    pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
      (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b))

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PoissonSchedules
open scoped BigOperators Classical NNReal
noncomputable section
variable {A : Type*}

lemma constant_mean (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    (∑ _i : Fin R×S,(γ:ℝ))=(R:ℝ)*S.card*γ := by
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,
    nsmul_eq_mul,Nat.cast_mul]

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*} [Fintype α]

omit [Fintype α] in

lemma own_inter (S T : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own (S∩T) U bs x=S∩own T U bs x := by
  induction bs generalizing T with
  | nil => simp [own]
  | cons b bs ih =>
    by_cases hx : x∈U b
    · simp [own,hx,inter_assoc]
    · simp only [own,ite_eq_right hx]
      rw [show (S∩T)\U b=S∩(T\U b) by ext y; simp only [mem_sdiff,mem_inter]; tauto,ih]

lemma own_public (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x=S∩own univ U bs x := by
  simpa using own_inter S univ U bs x

omit [Fintype α] in
lemma sized_planes (S : Finset α) (U : β → Finset α) (bs : List β) :
    (sized S U bs).map Prod.fst=bs := by
  induction bs generalizing S with
  | nil => rfl
  | cons b bs ih => simp [sized,ih]

omit [Fintype α] in
lemma publicSize_eq (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    publicSize U (sized S U bs) x=(own S U bs x).card := by
  induction bs generalizing S with
  | nil => simp [sized,publicSize,own]
  | cons b bs ih =>
    by_cases hx : x∈U b
    · simp [sized,publicSize,own,hx]
    · simp [sized,publicSize,own,hx,ih]

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.PreparedDecoder
open Finset SharpLogRamsey.PreparedRow SharpLogRamsey.PointScore
open SharpLogRamsey.GreedyPreparation
open scoped Classical BigOperators
noncomputable section
variable {A H B : Type*} [Fintype A] [Fintype H]

lemma publicSample_eq (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    publicSample (counts S ω)=sample S ω := by
  ext x
  by_cases hx : x∈S
  · constructor
    · intro hh
      exact mem_filter.mpr ⟨hx,(mem_filter.mp hh).2⟩
    · intro hh
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hh).2⟩
  · constructor
    · intro hh
      obtain ⟨r,hr⟩ := (mem_filter.mp hh).2
      exact False.elim (hr (by simp [counts,extend,hx]))
    · intro hh
      exact False.elim (hx (mem_filter.mp hh).1)

omit [Fintype A] in
lemma empty_counts (S : Finset A) (Q : A → Prop) {R : ℕ} (ω : Schedule S R) (r : Fin R) :
    (∀ y,Q y → counts S ω (r,y)=0) ↔ (∀ y : S,Q y.1 → ω (r,y)=0) := by
  constructor
  · intro h y hy
    simpa only [counts,extend,dite_eq_left y.2] using h y.1 hy
  · intro h y hy
    by_cases hs : y∈S
    · simpa only [counts,extend,dite_eq_left hs] using h ⟨y,hs⟩ hy
    · simp [counts,extend,hs]

omit [Fintype H] in
lemma publicScore_eq (S O : Finset A) (Q : A → Prop)
    (hQ : ∀ y∈S,(y∈O ↔ Q y)) (T : Finset H) (inc : H → A → Prop)
    (b : ℝ) {R : ℕ} (ω : Schedule S R) :
    publicScore Q T inc b (counts S ω)=score S O T inc b ω := by
  rw [publicScore,score_eq]
  apply sum_congr rfl
  intro h _
  apply prod_congr rfl
  intro r _
  simp only [empty_counts,pointEmpty]
  have he₁ : (∀ y : S,Q y.1 ∧ inc h y.1 → ω (r,y)=0) ↔
      (∀ y : S,y.1∈O ∧ inc h y.1 → ω (r,y)=0) := by
    simp only [←hQ _ (Subtype.prop _)]
  have he₂ : (∀ y : S,¬Q y.1 ∧ inc h y.1 → ω (r,y)=0) ↔
      (∀ y : S,y.1∉O ∧ inc h y.1 → ω (r,y)=0) := by
    simp only [←hQ _ (Subtype.prop _)]
  simp only [he₁,he₂]
  split_ifs <;> rfl

omit [Fintype H] in
theorem decode_equals_source (S₀ S : Finset A) (hS : S⊆S₀)
    (U : B → Finset A) (bs : List B) (T : A → Finset H) (inc : H → A → Prop)
    (L q : ℝ) (z : ℕ) {R : ℕ} (ω : Schedule S R) :
    decode U (sized S₀ U bs) S.card z T inc L q (counts S ω)=
      LearningRow.test (sample S ω)
        (fun x => score S (own S₀ U bs x) (T x) inc
          (Real.exp (-L*(1-((own S₀ U bs x).card:ℝ)/(S.card:ℝ)))) ω) z q := by
  rw [decode,publicSample_eq,sized_planes]
  congr 1
  funext x
  rw [publicSize_eq]
  apply publicScore_eq
  intro y hy
  rw [own_public,mem_inter]
  exact and_iff_right (hS hy)

end
end SharpLogRamsey.PreparedDecoder

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedProposals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.PublicTables
open MeasureTheory Finset
open scoped Classical BigOperators
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [Fintype Y]

lemma acceptProb_fromMeasure (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y)
    (hf : ∀ y,MeasurableSet (f ⁻¹' {y})) (A : Y → Prop) :
    acceptProb (Law.fromMeasure μ f hf) A=μ.real {x | A (f x)} := by
  unfold acceptProb accepted Law.fromMeasure
  simp only [mul_one]
  rw [←sum_filter]
  have h := sum_measureReal_preimage_singleton (μ:=μ) (univ.filter A) (fun y _ => hf y)
  simpa using h

end
end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.FiniteSchedules
open Finset MeasureTheory
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma coordinate_le_total (ω : ι → ℕ) (i : ι) : ω i ≤ total ω :=
  single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)

lemma clip_eq_iff (M : ℕ) (ω : ι → ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    clip M ω=z ↔ ω=(fun i => (z i:ℕ)) := by
  constructor
  · intro h
    funext i
    have he : min (ω i) (M+1)=(z i:ℕ) := congrArg Fin.val (congrFun h i)
    have hi := (coordinate_le_total (fun i => (z i:ℕ)) i).trans hz
    omega
  · rintro rfl
    funext i
    apply Fin.ext
    have hi := (coordinate_le_total (fun i => (z i:ℕ)) i).trans hz
    change min (z i:ℕ) (M+1)=(z i:ℕ)
    omega

lemma clip_preimage (M : ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    clip M ⁻¹' {z}={fun i => (z i:ℕ)} := by
  ext ω
  exact clip_eq_iff M ω z hz

lemma clip_total_iff (M : ℕ) (ω : ι → ℕ) :
    total (fun i => (clip M ω i:ℕ))≤M ↔ total ω≤M := by
  constructor
  · intro h
    have he := (clip_eq_iff M ω (clip M ω) h).mp rfl
    exact (congrArg total he).le.trans h
  · intro h
    unfold total clip
    have hi : ∀ i,min (ω i) (M+1)=ω i := fun i => by
      have hh := (coordinate_le_total ω i).trans h
      omega
    simp_rw [hi]
    exact h

lemma acceptance_preimage (M : ℕ) (P : (ι → ℕ) → Prop) :
    {ω | total (fun i => (clip M ω i:ℕ))≤M ∧ P (fun i => (clip M ω i:ℕ))}=
      {ω | total ω≤M ∧ P ω} := by
  ext ω
  constructor
  · rintro ⟨h,hp⟩
    have he := (clip_eq_iff M ω (clip M ω) h).mp rfl
    exact ⟨(clip_total_iff M ω).mp h,he ▸ hp⟩
  · rintro ⟨h,hp⟩
    have hc := (clip_total_iff M ω).mpr h
    have he := (clip_eq_iff M ω (clip M ω) hc).mp rfl
    exact ⟨hc,he ▸ hp⟩

end
end SharpLogRamsey.FiniteSchedules

namespace SharpLogRamsey.PoissonLikelihood
open MeasureTheory ProbabilityTheory Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem singleton_formula (rate : ι → ℝ≥0) (ω : ι → ℕ) :
    (law rate).real {ω} = Real.exp (-(∑ i,(rate i:ℝ))) *
      (∏ i,(rate i:ℝ)^(ω i))/(∏ i,((ω i).factorial:ℝ)) := by
  simp only [law,Measure.real,Measure.pi_singleton,ENNReal.toReal_prod,
    poissonMeasure_singleton,ENNReal.toReal_ofReal (show 0 ≤ Real.exp (-(rate _ : ℝ)) *
      (rate _ : ℝ)^ω _ /((ω _).factorial:ℝ) from by positivity)]
  rw [prod_div_distrib,prod_mul_distrib,←Real.exp_sum,sum_neg_distrib]

theorem singleton_ratio (proposal hidden : ι → ℝ≥0) (c : ℝ) (ω : ι → ℕ)
    (htotal : (∑ i,(proposal i:ℝ))=∑ i,(hidden i:ℝ))
    (hp : ∀ i,(proposal i:ℝ)^ω i=c^ω i*(hidden i:ℝ)^ω i) :
    (law proposal).real {ω}=c^(∑ i,ω i)*(law hidden).real {ω} := by
  rw [singleton_formula,singleton_formula,htotal]
  simp_rw [hp]
  rw [prod_mul_distrib,prod_pow_eq_pow_sum]
  ring

lemma sum_uniformRate (S : Finset ι) (a : ℝ≥0) (hS : S.Nonempty) :
    (∑ i,(uniformRate S a i:ℝ))=a := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hS)
  simp only [uniformRate,apply_ite,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_zero]
  rw [←sum_filter]
  simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
  field_simp

theorem uniform_singleton_ratio (S U : Finset ι) (a : ℝ≥0) (hS : S.Nonempty)
    (hU : U.Nonempty) (hSU : S ⊆ U) (ω : ι → ℕ) (hω : ∀ i,i∉S → ω i=0) :
    (law (uniformRate U a)).real {ω}=
      ((S.card:ℝ)/(U.card:ℝ))^(∑ i,ω i)*(law (uniformRate S a)).real {ω} := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hS)
  have hu : (U.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hU)
  apply singleton_ratio
  · rw [sum_uniformRate U a hU,sum_uniformRate S a hS]
  · intro i
    by_cases hi : i∈S
    · simp only [uniformRate,ite_eq_left hi,ite_eq_left (hSU hi),NNReal.coe_div,NNReal.coe_natCast]
      rw [←mul_pow]
      congr 1
      field_simp
    · rw [hω i hi]
      simp

end
end SharpLogRamsey.PoissonLikelihood

namespace SharpLogRamsey.PreparedProposals
open MeasureTheory ProbabilityTheory Finset
open SharpLogRamsey.PoissonLikelihood SharpLogRamsey.FiniteSchedules SharpLogRamsey.PublicTables
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma proposal_mass (U : Finset ι) (a : ℝ≥0) (M : ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    (proposal U a M).mass z=(law (uniformRate U a)).real {fun i => (z i:ℕ)} := by
  change (law _).real (clip M ⁻¹' {z})=_
  rw [clip_preimage M z hz]

theorem atom_domination (S U : Finset ι) (a : ℝ≥0) (M : ℕ)
    (hS : S.Nonempty) (hU : U.Nonempty) (hSU : S⊆U) (P : (ι → ℕ) → Prop)
    (z : ι → Fin (M+2)) (hz : accepts S M P z) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(proposal S a M).mass z ≤ (proposal U a M).mass z := by
  rw [proposal_mass S a M z hz.1,proposal_mass U a M z hz.1,
    uniform_singleton_ratio S U a hS hU hSU _ hz.2.1]
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  apply pow_le_pow_of_le_one (by positivity) _ hz.1
  apply (div_le_one (by exact_mod_cast card_pos.mpr hU)).mpr
  exact_mod_cast card_le_card hSU

lemma accepts_probability (S : Finset ι) (a : ℝ≥0) (M : ℕ) (P : (ι → ℕ) → Prop) :
    acceptProb (proposal S a M) (accepts S M P)=
      (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} := by
  rw [proposal,acceptProb_fromMeasure]
  rw [show {x | accepts S M P (clip M x)}=
    {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} by
      exact acceptance_preimage M (fun ω => (∀ i,i∉S → ω i=0) ∧ P ω)]

theorem proposal_success (S U : Finset ι) (a : ℝ≥0) (M : ℕ)
    (hS : S.Nonempty) (hU : U.Nonempty) (hSU : S⊆U) (P : (ι → ℕ) → Prop) :
    ((S.card:ℝ)/(U.card:ℝ))^M *
      (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} ≤
      acceptProb (proposal U a M) (accepts S M P) := by
  rw [←accepts_probability]
  unfold acceptProb accepted
  simp only [mul_one]
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  by_cases hz : accepts S M P z
  · simp only [ite_eq_left hz]
    exact atom_domination S U a M hS hU hSU P z hz
  · simp [hz]

lemma hidden_support_ae (S : Finset ι) (a : ℝ≥0) :
    ∀ᵐ ω ∂law (uniformRate S a),∀ i,i∉S → ω i=0 := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i∈S
  · filter_upwards [] with ω using (fun h => False.elim (h hi))
  · have hp := measurePreserving_eval (fun j => poissonMeasure (uniformRate S a j)) i
    have hx : ∀ᵐ n ∂poissonMeasure (uniformRate S a i),n=0 := by
      rw [uniformRate,ite_eq_right hi]
      apply (ae_iff_prob_eq_one (measurable_of_countable (fun n : ℕ => n=0))).mpr
      change (poissonMeasure 0) {0}=1
      rw [poissonMeasure_singleton]
      norm_num
    exact (hp.quasiMeasurePreserving.ae hx).mono (fun ω h _ => h)

lemma true_success_probability (S : Finset ι) (a : ℝ≥0) (M : ℕ) (P : (ι → ℕ) → Prop) :
    (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω}=
      (law (uniformRate S a)).real {ω | total ω≤M ∧ P ω} := by
  apply measureReal_congr
  filter_upwards [hidden_support_ae S a] with ω hω
  apply propext
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hω, h.2⟩⟩

end
end SharpLogRamsey.PreparedProposals

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedPointProposals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
noncomputable section
variable {A : Type*} [Fintype A]

local instance flat_JoinedPreparedPointProposals_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R×A) := Classical.decEq _
omit [Fintype A] in

theorem total_cutoff_intersection (S : Finset A) (R M : ℕ) (γ : ℝ≥0)
    (P : Set (Schedule S R)) (hM : 2*((R:ℝ)*S.card*γ)≤M) :
    (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real P-
      Real.exp (-((R:ℝ)*S.card*γ)/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real
        {ω | (∑ i,ω i)≤M ∧ ω∈P} := by
  let μ := PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)
  have ht := PoissonTail.total_tail (fun _ : Fin R×S => γ)
  rw [constant_mean S R γ] at ht
  have hbad : μ.real {ω | M<∑ i,ω i}≤Real.exp (-((R:ℝ)*S.card*γ)/3) := by
    apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) ht
    intro ω hω
    exact hM.trans (by exact_mod_cast hω.le)
  have hs : P⊆{ω | (∑ i,ω i)≤M ∧ ω∈P}∪{ω | M<∑ i,ω i} := by
    intro ω hω
    by_cases hc : (∑ i,ω i)≤M
    · exact Or.inl ⟨hc,hω⟩
    · exact Or.inr (Nat.lt_of_not_ge hc)
  have hu := (measureReal_mono (μ:=μ) (h₂:=measure_ne_top _ _) hs).trans
    (measureReal_union_le _ _)
  linarith

omit [Fintype A] in
lemma ambientCounts_restrict (S : Finset A) {R : ℕ} (z : Fin R×A → ℕ)
    (hz : ∀ rx,rx.2∉S → z rx=0) :
    ambientCounts S (fun rx : Fin R×S => z (rx.1,rx.2))=z := by
  funext rx
  by_cases hx : rx.2∈S
  · simp [ambientCounts,extend,hx]
  · simp [ambientCounts,extend,hx,hz rx hx]

omit [Fintype A] in
lemma restrict_ambientCounts (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    (fun rx : Fin R×S => ambientCounts S ω (rx.1,rx.2))=ω := by
  funext rx
  simp [ambientCounts,extend,rx.2.2]

theorem ambientCounts_hasLaw (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    HasLaw (ambientCounts S) (PoissonSchedules.scheduleLaw (ambientRate S R γ))
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton z)]
  by_cases hz : ∀ rx,rx.2∉S → z rx=0
  · have he : ambientCounts S ⁻¹' {z}={fun rx : Fin R×S => z (rx.1,rx.2)} := by
      ext ω
      simp only [Set.mem_preimage,Set.mem_singleton_iff]
      constructor
      · intro h
        calc
          ω = fun rx : Fin R×S => ambientCounts S ω (rx.1,rx.2) := (restrict_ambientCounts S ω).symm
          _ = _ := by rw [h]
      · rintro rfl
        exact ambientCounts_restrict S z hz
    rw [he,PoissonSchedules.scheduleLaw,PoissonSchedules.scheduleLaw,
      Measure.pi_singleton,Measure.pi_singleton,Fintype.prod_prod_type,Fintype.prod_prod_type]
    apply prod_congr rfl
    intro r _
    calc
      _ = ∏ x∈S,poissonMeasure γ {z (r,x)} := prod_coe_sort S _
      _ = ∏ x∈S,poissonMeasure (ambientRate S R γ (r,x)) {z (r,x)} := by
        apply prod_congr rfl
        intro x hx
        rw [ambientRate,ite_eq_left hx]
      _ = _ := prod_subset (subset_univ S) (fun x _ hx => by
        simp only [ambientRate,ite_eq_right hx,hz (r,x) hx,poissonMeasure_singleton]
        norm_num)
  · obtain ⟨rx,hx,hn⟩ := not_forall.mp hz |>.imp (fun rx h => by simpa using h)
    have he : ambientCounts S ⁻¹' {z}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hh := congrFun (Set.mem_singleton_iff.mp hω) rx
      exact hn (by simpa [ambientCounts,extend,hx] using hh.symm)
    rw [he,measure_empty,PoissonSchedules.scheduleLaw,Measure.pi_singleton]
    symm
    apply prod_eq_zero (mem_univ rx)
    simp [ambientRate,hx,poissonMeasure_singleton,hn]

lemma sum_ambientCounts (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    (∑ rx,ambientCounts S ω rx)=∑ rx,ω rx := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  change (∑ x,PoissonSupport.extend S (fun x => ω (r,x)) x)=_
  exact PoissonSupport.sum_extend S _

omit [Fintype A] in
lemma ambient_rate_uniform (S : Finset A) (hS : S.Nonempty) (R : ℕ) (hR : 0<R)
    (γ : ℝ≥0) :
    PoissonLikelihood.uniformRate (coordinateSupport S R) ((R:ℝ≥0)*S.card*γ)=
      ambientRate S R γ := by
  funext rx
  simp only [PoissonLikelihood.uniformRate,coordinateSupport,mem_product,mem_univ,true_and,
    card_product,card_univ,Fintype.card_fin,ambientRate]
  by_cases hx : rx.2∈S
  · simp only [ite_eq_left hx,Nat.cast_mul]
    have hr : (R:ℝ≥0)≠0 := by exact_mod_cast hR.ne'
    have hs : (S.card:ℝ≥0)≠0 := by exact_mod_cast (card_pos.mpr hS).ne'
    field_simp
  · simp only [ite_eq_right hx]

theorem ambient_proposal_success (S U : Finset A) (hS : S.Nonempty) (hSU : S⊆U)
    (R M : ℕ) (hR : 0<R) (γ : ℝ≥0) (P : (Fin R×A→ℕ)→Prop) :
    ((S.card:ℝ)/(U.card:ℝ))^M *
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real
        {ω | (∑ i,ω i)≤M ∧ P (ambientCounts S ω)} ≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*γ) M)
        (PreparedProposals.accepts (coordinateSupport S R) M P) := by
  have hu : U.Nonempty := hS.mono hSU
  have hcS : (coordinateSupport S R).Nonempty := by
    exact Finset.Nonempty.product (by exact ⟨⟨0,hR⟩,mem_univ _⟩) hS
  have hcU : (coordinateSupport U R).Nonempty := hcS.mono (product_subset_product_right hSU)
  have hcSU : coordinateSupport S R⊆coordinateSupport U R := product_subset_product_right hSU
  have hh := PreparedProposals.proposal_success (coordinateSupport S R) (coordinateSupport U R)
    ((R:ℝ≥0)*S.card*γ) M hcS hcU hcSU P
  rw [PreparedProposals.true_success_probability,ambient_rate_uniform S hS R hR γ] at hh
  have he : ((coordinateSupport S R).card:ℝ)/((coordinateSupport U R).card:ℝ)=
      (S.card:ℝ)/(U.card:ℝ) := by
    simp only [coordinateSupport,card_product,card_univ,Fintype.card_fin,Nat.cast_mul]
    have hr : (R:ℝ)≠0 := by exact_mod_cast hR.ne'
    field_simp
  rw [he] at hh
  have hlaw := ambientCounts_hasLaw S R γ
  have hm := congrArg (fun μ : Measure (Fin R×A→ℕ) =>
    μ.real {z | FiniteSchedules.total z≤M ∧ P z}) hlaw.map_eq
  rw [map_measureReal_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)] at hm
  have hp : ambientCounts S ⁻¹' {z | FiniteSchedules.total z≤M ∧ P z}=
      {ω | (∑ i,ω i)≤M ∧ P (ambientCounts S ω)} := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,FiniteSchedules.total,sum_ambientCounts]
  rw [hp] at hm
  exact hm.symm ▸ hh

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPreparedDescription_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PreparedDescription.flat_JoinedPreparedDescription_3
attribute [local instance] OAI.SharpLogRamsey.PreparedDescription.flat_JoinedPreparedDescription_4
lemma good_of_source (S₀ S : Finset (Projectivization K V)) (hS : S⊆S₀)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E : Finset (Projectivization K (Module.Dual K V))) (L cap size : ℝ)
    {R : ℕ} (ω : Schedule S R)
    (hcap : cap≤(S∩rowTest S (own S₀ plane bs) E
      (fun x => Real.exp (-L*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))) ω).card)
    (hsize : ((rowTest S (own S₀ plane bs) E
      (fun x => Real.exp (-L*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))) ω).card:ℝ)≤ size) :
    good S plane (sized S₀ plane bs) L cap size (ambientCounts S ω) := by
  refine ⟨(emptySet S E inc ω).card,card_le_univ _,?_⟩
  dsimp only
  have he := PreparedDecoder.decode_equals_source S₀ S hS plane bs pencil inc L
    (Nat.card K) (emptySet S E inc ω).card ω
  change _ = rowTest S (own S₀ plane bs) E _ ω at he
  change cap≤(S∩PreparedDecoder.decode _ _ _ _ _ _ _ _ (PreparedDecoder.counts S ω)).card ∧
    ((PreparedDecoder.decode _ _ _ _ _ _ _ _ (PreparedDecoder.counts S ω)).card:ℝ)≤ size
  rw [he]
  exact ⟨hcap,hsize⟩

theorem geometric_proposal_probability
    (n R p h M : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S₀ S U Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty)
    (hS₀ : S⊆S₀) (hSU : S⊆U) (hDa : Ds⊆Da)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (hf : ∀ x,((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)≤1/25)
    (B₀ C bE δ u zmin W tS tA : ℝ)
    (hδ : 0≤δ) (hu : 0<u) (hzmin : 0<zmin) (htS : 0<tS) (htA : 0<tA)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : Real.exp (3*((L:ℝ)*R))≤B₀)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*Real.exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤bE)
    (hW : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : zmin≤(E₀.card:ℝ)*Real.exp (-bE)/2)
    (herror : ∀ x,x∉Ds → Real.exp (-(L:ℝ)*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤zmin/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ T a)
    (hM : 2*((R:ℝ)*S.card*(L*c:ℝ≥0))≤M) :
    let q : ℝ := Nat.card K
    let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
    let t := zmin/(10*q)
    let εs := B₀^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
    let εa := B₀^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
    let lower := Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
      (S.card:ℝ)*εs/tS-(Fintype.card (Projectivization K V):ℝ)*εa/tA-2*Real.exp (-μmean/3)
    let cap := (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)
    let size := 2*μmean+(Da.card:ℝ)+tA+100*q^(n+3)/zmin
    ((S.card:ℝ)/(U.card:ℝ))^M*lower≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (good S plane (sized S₀ plane bs) L cap size)) := by
  dsimp only
  let O := own S₀ plane bs
  let f := fun x => ((O x).card:ℝ)/(S.card:ℝ)
  have hr := geometric_row_probability n R p h hn hdim S Ds Da hS hDa O E E₀ hE₀ hE₀E
    c L hc f hf B₀ C bE δ u zmin W tS tA hδ hu hzmin htS htA hC hL hR hp hpe hB hQ
    hα hsmall hW hZ herror T a hs ha
  dsimp only at hr
  let P := {ω : Schedule S R | ∃ z≤Fintype.card (Projectivization K (Module.Dual K V)),
    let W₀ := PreparedDecoder.decode plane (sized S₀ plane bs) S.card z pencil inc L (Nat.card K) (ambientCounts S ω)
    (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)≤(S∩W₀).card ∧
    (W₀.card:ℝ)≤2*((R:ℝ)*S.card*(L*c:ℝ≥0))+(Da.card:ℝ)+tA+100*(Nat.card K:ℝ)^(n+3)/zmin}
  have hp' : Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
      (S.card:ℝ)*(B₀^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/(zmin/(10*(Nat.card K:ℝ)))^2)/tS-
      (Fintype.card (Projectivization K V):ℝ)*(B₀^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/(zmin/(10*(Nat.card K:ℝ)))^p)/tA-
      Real.exp (-((R:ℝ)*S.card*(L*c:ℝ≥0))/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real P := by
    apply hr.trans
    apply measureReal_mono (h₂:=measure_ne_top _ _)
    intro ω hω
    exact good_of_source S₀ S hS₀ plane bs E L _ _ ω hω.2.1 hω.2.2
  have hcut := total_cutoff_intersection S R M (L*c) P hM
  have hprop := ambient_proposal_success S U hS hSU R M (by omega) (L*c)
    (good S plane (sized S₀ plane bs) L
      ((S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ))
      (2*((R:ℝ)*S.card*(L*c:ℝ≥0))+(Da.card:ℝ)+tA+100*(Nat.card K:ℝ)^(n+3)/zmin))
  apply le_trans _ hprop
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change _≤(PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real {ω | (∑ i,ω i)≤M ∧ ω∈P}
  linarith

end
end SharpLogRamsey.PreparedDescription

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedTypical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedTypical
open Finset PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {A : Type*}

lemma outside_count (S O : Finset A) (hO : O⊆S) (x : A) (R : A→Prop) :
    (((S\(O∪{x})).filter R).card:ℝ) ≤ (S.filter R).card-(O.filter R).card ∧
    (S.filter R).card-(O.filter R).card-1 ≤ (((S\(O∪{x})).filter R).card:ℝ) := by
  have he : (S\(O∪{x})).filter R = ((S.filter R)\(O.filter R)).erase x := by
    ext y
    simp only [mem_filter,mem_sdiff,mem_union,mem_singleton,mem_erase]
    aesop
  have ho : O.filter R⊆S.filter R := filter_subset_filter R hO
  have hk := card_sdiff_add_card_eq_card ho
  have hn : (((S.filter R)\(O.filter R)).erase x).card ≤ ((S.filter R)\(O.filter R)).card :=
    card_le_card (erase_subset _ _)
  have hl : ((S.filter R)\(O.filter R)).card ≤ (((S.filter R)\(O.filter R)).erase x).card+1 := by
    by_cases hx : x∈((S.filter R)\(O.filter R))
    · rw [card_erase_of_mem hx]; omega
    · rw [erase_eq_of_notMem hx]; omega
  rw [he]
  have hk' : (((S.filter R)\(O.filter R)).card:ℝ)+(O.filter R).card=(S.filter R).card := by exact_mod_cast hk
  have hn' : ((((S.filter R)\(O.filter R)).erase x).card:ℝ)≤((S.filter R)\(O.filter R)).card := by exact_mod_cast hn
  have hl' : (((S.filter R)\(O.filter R)).card:ℝ)≤(((S.filter R)\(O.filter R)).erase x).card+1 := by exact_mod_cast hl
  constructor <;> linarith

lemma outside_scalar (c f l o r : ℝ) (_hc : 0 ≤ c) (hc1 : c≤1/100)
    (hf0 : 0≤f) (hf : f≤1/25)
    (hl : |l-1|≤1/10) (ho : |o-f|≤1/50)
    (hr₁ : r≤l-o) (hr₂ : l-o-c ≤ r) :
    3/4 ≤ r ∧ r≤2 ∧ |r-(1-f)|≤13/100 := by
  rw [abs_le] at hl ho ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma outside_square (c f l o r : ℝ) (hc : 0 ≤ c)
    (hr₁ : r≤l-o) (hr₂ : l-o-c ≤ r) :
    (r-(1-f))^2≤3*((l-1)^2+(o-f)^2+c^2) := by
  have he₁ : 0≤l-o-r := by linarith
  have he₂ : l-o-r ≤ c := by linarith
  have hes : (l-o-r)^2 ≤ c^2 := by nlinarith
  nlinarith [sq_nonneg ((l-1)+(o-f)),sq_nonneg ((l-1)+(l-o-r)),
    sq_nonneg ((o-f)-(l-o-r))]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma outside_mass_between (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0) (H : Projectivization K (Module.Dual K V)) :
    outsideMass S O x c H≤ mass S c H-mass O c H ∧
    mass S c H-mass O c H-c≤ outsideMass S O x c H := by
  have he : (S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule≤LinearMap.ker H.rep) =
      (S\(O∪{x})).filter (fun y => y.submodule≤LinearMap.ker H.rep) := by
    ext y
    simp only [mem_filter,mem_sdiff,mem_union,mem_singleton]
    aesop
  have hh := outside_count S O hO x (fun y => y.submodule≤LinearMap.ker H.rep)
  simp only [outsideMass,he,mass]
  constructor
  · have ht := mul_le_mul_of_nonneg_left hh.1 c.coe_nonneg
    linarith
  · have ht := mul_le_mul_of_nonneg_left hh.2 c.coe_nonneg
    linarith

omit [Finite K] [FiniteDimensional K V] in
theorem typical_point (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0) (H : Projectivization K (Module.Dual K V))
    (f : ℝ) (hc : (c:ℝ)≤1/100) (hf0 : 0≤f) (hf : f≤1/25)
    (hl : |mass S c H-1|≤1/10) (ho : |mass O c H-f|≤1/50) :
    3/4≤ outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-f)|≤13/100 := by
  have hh := outside_mass_between S O hO x c H
  exact outside_scalar c f _ _ _ c.coe_nonneg hc hf0 hf hl ho hh.1 hh.2

theorem typical_squares (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0)
    (T : Finset (Projectivization K (Module.Dual K V))) (hT : T⊆pencil x)
    (f U W : ℝ)
    (hl : ∀ H∈T,|mass S c H-1|≤1/10)
    (ho : ∀ H∈T,|mass O c H-f|≤1/50)
    (hU : (∑ H∈pencil x,min 1 ((mass S c H-1)^2))≤U)
    (hW : (∑ H∈pencil x,min 1 ((mass O c H-f)^2))≤W) :
    (∑ H∈T,(outsideMass S O x c H-(1-f))^2)≤
      3*(U+W+(T.card:ℝ)*(c:ℝ)^2) := by
  have hl' : (∑ H∈T,(mass S c H-1)^2)≤U := by
    calc
      _ = ∑ H∈T,min 1 ((mass S c H-1)^2) := by
        apply sum_congr rfl
        intro H hH
        have ht := hl H hH
        rw [min_eq_right]
        have hs := mul_self_le_mul_self (abs_nonneg (mass S c H-1)) ht
        nlinarith [sq_abs (mass S c H-1)]
      _ ≤ ∑ H∈pencil x,min 1 ((mass S c H-1)^2) :=
        sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => le_min (by norm_num) (sq_nonneg _))
      _ ≤ U := hU
  have ho' : (∑ H∈T,(mass O c H-f)^2)≤W := by
    calc
      _ = ∑ H∈T,min 1 ((mass O c H-f)^2) := by
        apply sum_congr rfl
        intro H hH
        have ht := ho H hH
        rw [min_eq_right]
        have hs := mul_self_le_mul_self (abs_nonneg (mass O c H-f)) ht
        nlinarith [sq_abs (mass O c H-f)]
      _ ≤ ∑ H∈pencil x,min 1 ((mass O c H-f)^2) :=
        sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => le_min (by norm_num) (sq_nonneg _))
      _ ≤ W := hW
  calc
    _ ≤ ∑ H∈T,3*((mass S c H-1)^2+(mass O c H-f)^2+(c:ℝ)^2) := by
      apply sum_le_sum
      intro H _
      have hh := outside_mass_between S O hO x c H
      exact outside_square c f _ _ _ c.coe_nonneg hh.1 hh.2
    _ = 3*((∑ H∈T,(mass S c H-1)^2)+(∑ H∈T,(mass O c H-f)^2)+(T.card:ℝ)*(c:ℝ)^2) := by
      simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul]
    _ ≤ _ := by linarith

end
end SharpLogRamsey.PreparedTypical

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence
noncomputable section
variable {A : Type*} [Fintype A]

lemma sum_center_shift (f : A → ℝ) (μ a : ℝ) :
    (∑ x,(f x-a)^2) ≤ 2*∑ x,(f x-μ)^2 +
      2*(Fintype.card A:ℝ)*(μ-a)^2 := by
  calc
    _ ≤ ∑ x, (2*(f x-μ)^2+2*(μ-a)^2) := by
      apply sum_le_sum
      intro x _
      nlinarith [sq_nonneg ((f x-μ)-(μ-a))]
    _ = _ := by rw [sum_add_distrib,←mul_sum]; simp; ring

lemma indicator_sum (C : Finset A) (c : ℝ) :
    (∑ x,if x ∈ C then c else 0) = (C.card:ℝ)*c := by
  rw [←sum_filter]
  simp

lemma indicator_square_sum (C : Finset A) (c : ℝ) :
    (∑ x,(if x ∈ C then c else 0)^2) = (C.card:ℝ)*c^2 := by
  simp_rw [ite_pow,zero_pow (by decide : 2≠0)]
  exact indicator_sum C (c^2)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem cell_total_variance {n : ℕ} (hdim : Module.finrank K V=n+3)
    (C : Finset (Projectivization K V)) (N : ℝ) (hN : 0<N) :
    (∑ H : Projectivization K (Module.Dual K V),
      (weightedIncidences SharpLogRamsey.Incidence.Incident (fun x => if x∈C then (Nat.card K:ℝ)/N else 0) H -
        (C.card:ℝ)/N)^2) ≤ 4*(Nat.card K:ℝ)^(n+3)*(C.card:ℝ)/N^2 := by
  let q : ℝ := Nat.card K
  let Q : ℝ := ∑ i ∈ range (n+3),q^i
  let u : ℝ := ∑ i ∈ range (n+2),q^i
  let w : Projectivization K V → ℝ := fun x => if x∈C then q/N else 0
  have hq : 1≤q := by
    dsimp [q]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α:=K)).ne')
  have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hQ : Q=q*u+1 := by dsimp [Q,u]; rw [geom_sum_succ]
  have hu : 0≤u := by dsimp [u]; positivity
  have hQ0 : 0<Q := by nlinarith
  have hvcard : (Fintype.card (Projectivization K (Module.Dual K V)):ℝ)=Q := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K _
      (Subspace.dual_finrank_eq.trans hdim)]
    push_cast; rfl
  have hpcard : (Fintype.card (Projectivization K V):ℝ)=Q := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K _ hdim]
    push_cast; rfl
  have hcQ : (C.card:ℝ)≤Q := by
    rw [←hpcard]
    exact_mod_cast card_le_univ C
  have hc0 : (0:ℝ)≤C.card := Nat.cast_nonneg _
  have hs : ∑ x,w x = (C.card:ℝ)*(q/N) := indicator_sum C (q/N)
  have hs2 : ∑ x,w x^2 = (C.card:ℝ)*(q/N)^2 := indicator_square_sum C (q/N)
  let μ : ℝ := u/Q * ∑ x,w x
  have hshift : μ-(C.card:ℝ)/N = -(C.card:ℝ)/(Q*N) := by
    dsimp [μ]
    rw [hs]
    field_simp
    nlinarith [hQ]
  have hvar := projective_variance_le hdim w
  change (∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-μ)^2) ≤ q^(n+1)*∑ x,w x^2 at hvar
  rw [hs2] at hvar
  have hshiftbound : Q*(μ-(C.card:ℝ)/N)^2 ≤ (C.card:ℝ)/N^2 := by
    rw [hshift]
    apply (le_of_mul_le_mul_left ?_ (mul_pos hQ0 (sq_pos_of_pos hN)))
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hcQ hc0]
  have hpow : 1≤q^(n+3) := one_le_pow₀ hq
  have hexact : q^(n+1)*((C.card:ℝ)*(q/N)^2) = q^(n+3)*(C.card:ℝ)/N^2 := by
    rw [show n+3=(n+1)+2 by omega,pow_add]; field_simp; ring
  have hmain := sum_center_shift (fun H => weightedIncidences SharpLogRamsey.Incidence.Incident w H) μ ((C.card:ℝ)/N)
  rw [hvcard] at hmain
  change (∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-(C.card:ℝ)/N)^2) ≤ _
  calc
    _ ≤ 2*(∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-μ)^2)+2*Q*(μ-(C.card:ℝ)/N)^2 := hmain
    _ ≤ 2*(q^(n+1)*((C.card:ℝ)*(q/N)^2))+2*((C.card:ℝ)/N^2) := by nlinarith
    _ ≤ 4*q^(n+3)*(C.card:ℝ)/N^2 := by
      rw [hexact]
      have hh := mul_le_mul_of_nonneg_right hpow (show 0≤(C.card:ℝ)/N^2 by positivity)
      have hh' : (C.card:ℝ)/N^2 ≤ q^(n+3)*(C.card:ℝ)/N^2 := by
        simpa only [one_mul,mul_div_assoc] using hh
      calc
        _ ≤ 2*(q^(n+3)*(C.card:ℝ)/N^2)+
            2*(q^(n+3)*(C.card:ℝ)/N^2) := by gcongr
        _ = _ := by ring

end
end SharpLogRamsey.RegularPencils

namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A ι : Type*} [Fintype A] [Fintype ι]

lemma exceptional_indicator (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ) (H : A) :
    (if H∈exceptional l c f then (1:ℝ) else 0)  ≤
      100*(l H-1)^2+2500*∑ i,(c i H-f i)^2 := by
  split_ifs with he
  · rcases (mem_filter.mp he).2 with hl | ⟨i,hi⟩
    · have hs : (1/10:ℝ)^2  <  (l H-1)^2 := by nlinarith [sq_abs (l H-1)]
      have hp : 0  ≤  ∑ i,(c i H-f i)^2 := sum_nonneg (fun _ _ =>  sq_nonneg _)
      nlinarith
    · have hs : (1/50:ℝ)^2  <  (c i H-f i)^2 := by nlinarith [sq_abs (c i H-f i)]
      have hi' := single_le_sum (f:=fun i =>  (c i H-f i)^2)
        (fun _ _ =>  sq_nonneg _) (mem_univ i)
      nlinarith [sq_nonneg (l H-1)]
  · positivity

theorem exceptional_card (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ)
    (V W : ℝ) (hl : ∑ H,(l H-1)^2  ≤  V)
    (hc : ∑ i,∑ H,(c i H-f i)^2  ≤  W) :
    ((exceptional l c f).card:ℝ)  ≤  100*V+2500*W := by
  have hh := sum_le_sum (s:=univ) (fun H _ =>  exceptional_indicator l c f H)
  simp only [sum_add_distrib,←mul_sum] at hh
  rw [sum_comm] at hh
  have hi : (∑ H,if H∈exceptional l c f then (1:ℝ) else 0) =
      ((exceptional l c f).card:ℝ) := by rw [←sum_filter]; simp
  rw [hi] at hh
  linarith

theorem exceptional_mass (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ)
    (V W : ℝ) (hl : ∑ H,(l H-1)^2  ≤  V)
    (hc : ∑ i,∑ H,(c i H-f i)^2  ≤  W) :
    (∑ H∈exceptional l c f,l H)  ≤  201*V+5000*W := by
  have hcard := exceptional_card l c f V W hl hc
  calc
    _  ≤  ∑ H∈exceptional l c f,(2+(l H-1)^2) := by
      apply sum_le_sum
      intro H _
      nlinarith [sq_nonneg (l H-3/2)]
    _ = 2*((exceptional l c f).card:ℝ)+∑ H∈exceptional l c f,(l H-1)^2 := by
      rw [sum_add_distrib]; simp; ring
    _  ≤  2*((exceptional l c f).card:ℝ)+V := by
      gcongr
      exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ =>  sq_nonneg _)).trans hl
    _  ≤  _ := by linarith

lemma clip_nonneg (x : ℝ) : 0  ≤  min 1 (x^2) := le_min (by norm_num) (sq_nonneg _)
lemma clip_le_one (x : ℝ) : min 1 (x^2)  ≤  1 := min_le_left _ _
lemma clip_sum (x : A → ℝ) : (∑ H,min 1 ((x H)^2))  ≤  ∑ H,(x H)^2 :=
  sum_le_sum (fun _ _ =>  min_le_right _ _)

end
end SharpLogRamsey.RegularPencils

namespace SharpLogRamsey.PreparedVariance
open Finset PreparedRow PreparedTypical Incidence RegularPencils
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype I]

attribute [local instance] OAI.SharpLogRamsey.PreparedVariance.flat_JoinedPreparedVariance_2
attribute [local instance] OAI.SharpLogRamsey.PreparedVariance.flat_JoinedPreparedVariance_3
lemma mass_weighted (C : Finset (Projectivization K V)) (c : ℝ≥0)
    (H : Projectivization K (Module.Dual K V)) :
    mass C c H=weightedIncidences SharpLogRamsey.Incidence.Incident (fun x => if x∈C then (c:ℝ) else 0) H := by
  dsimp [mass,weightedIncidences]
  have he : (∑ x : Projectivization K V,if SharpLogRamsey.Incidence.Incident x H then (if x∈C then (c:ℝ) else 0) else 0)=
      ∑ x∈C.filter (fun y => y.submodule≤LinearMap.ker H.rep),(c:ℝ) := by
    rw [sum_filter]
    calc
      _ = ∑ x,if x∈C then (if x.submodule≤LinearMap.ker H.rep then (c:ℝ) else 0) else 0 := by
        apply sum_congr rfl
        intro x _
        simp only [_root_.OAI.SharpLogRamsey.Incidence.incident_iff_submodule]
        split_ifs <;> rfl
      _ = _ := by rw [←sum_filter]; simp
  rw [he]
  simp [mul_comm]

lemma actual_cell_variance {n : ℕ} (hdim : Module.finrank K V=n+3)
    (C : Finset (Projectivization K V)) (N : ℝ) (hN : 0<N)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/N) :
    (∑ H : Projectivization K (Module.Dual K V),(mass C c H-(C.card:ℝ)/N)^2)≤
      4*(Nat.card K:ℝ)^(n+3)*(C.card:ℝ)/N^2 := by
  have hh := cell_total_variance hdim C N hN
  simpa only [mass_weighted,hc] using hh

theorem actual_exceptions {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) :
    let E := exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ))
    let Q := (Nat.card K:ℝ)^(n+3)/(S.card:ℝ)
    (∑ H : Projectivization K (Module.Dual K V),(mass S c H-1)^2)≤4*Q ∧
    (∑ i,∑ H : Projectivization K (Module.Dual K V),
      (mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ))^2)≤4*Q ∧
    (E.card:ℝ)≤10400*Q ∧ (∑ H∈E,mass S c H)≤20804*Q := by
  dsimp only
  have hN : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hs := actual_cell_variance hdim S S.card hN c hc
  have hi (i : I) := actual_cell_variance hdim (C i) S.card hN c hc
  rw [div_self hN.ne'] at hs
  have hr : 4*(Nat.card K:ℝ)^(n+3)*(S.card:ℝ)/(S.card:ℝ)^2=
      4*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by field_simp
  rw [hr] at hs
  have htotal : (∑ i,∑ H : Projectivization K (Module.Dual K V),
      (mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ))^2)≤
        4*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by
    calc
      _ ≤ ∑ i,4*(Nat.card K:ℝ)^(n+3)*((C i).card:ℝ)/(S.card:ℝ)^2 :=
        sum_le_sum (fun i _ => hi i)
      _ = (4*(Nat.card K:ℝ)^(n+3)/(S.card:ℝ)^2)*(∑ i,((C i).card:ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ ≤ (4*(Nat.card K:ℝ)^(n+3)/(S.card:ℝ)^2)*(S.card:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hC
      _ = _ := by field_simp
  refine ⟨hs,htotal,?_,?_⟩
  · have h := exceptional_card (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) _ _ hs htotal
    linarith
  · have h := exceptional_mass (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) _ _ hs htotal
    linarith

lemma weights_nonneg (S : Finset (Projectivization K V)) (C : I→Finset (Projectivization K V))
    (c : ℝ≥0) (i : Option (Option I)) (H : Projectivization K (Module.Dual K V)) :
    0≤weights S C c i H := by
  cases i with
  | none => exact clip_nonneg _
  | some i => cases i with
    | none => dsimp [weights]; split_ifs <;> norm_num
    | some i => exact clip_nonneg _

lemma weights_le_one (S : Finset (Projectivization K V)) (C : I→Finset (Projectivization K V))
    (c : ℝ≥0) (i : Option (Option I)) (H : Projectivization K (Module.Dual K V)) :
    weights S C c i H≤1 := by
  cases i with
  | none => exact clip_le_one _
  | some i => cases i with
    | none => dsimp [weights]; split_ifs <;> norm_num
    | some i => exact clip_le_one _

lemma weights_total {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) :
    (∑ i,∑ H,weights S C c i H)≤10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by
  have hh := actual_exceptions hdim S hS C hC c hc
  dsimp only at hh
  have hs := clip_sum (fun H => mass S c H-1)
  have hi := sum_le_sum (s:=univ) (fun i _ => clip_sum (fun H => mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ)))
  simp only [Fintype.sum_option,weights]
  have he : (∑ H,if H∈exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) then (1:ℝ) else 0)=
      ((exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ))).card:ℝ) := by rw [←sum_filter]; simp
  rw [he]
  linarith [hh.1,hh.2.1,hh.2.2.1]

theorem exists_regular {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤T/2) :
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*(T/2)^2≤10408*(Nat.card K:ℝ)^(2*n+4)/(S.card:ℝ) ∧
      ∀ x∉D,∀ i,(∑ H∈pencil x,weights S C c i H)<T := by
  let D := univ.biUnion (fun i => univ.filter (fun x : Projectivization K V =>
    T≤∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0))
  have hp : (0:ℝ)≤(∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k) := by positivity
  have hmass := weights_total hdim S hS C hC c hc
  have hm (i : Option (Option I)) :
      (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*∑ H,weights S C c i H≤T/2 := by
    apply le_trans _ hmean
    apply mul_le_mul_of_nonneg_left _ hp
    apply le_trans _ hmass
    exact single_le_sum (fun j _ => sum_nonneg (fun H _ => weights_nonneg S C c j H)) (mem_univ i)
  have hd := pencil_family_tail hdim (weights S C c) (weights_nonneg S C c) (weights_le_one S C c) T hT hm
  refine ⟨D,?_,?_⟩
  · apply hd.trans
    calc
      _ ≤ (Nat.card K:ℝ)^(n+1)*(10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ))) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by rw [show 2*n+4=(n+1)+(n+3) by omega,pow_add]; ring
  · intro x hx i
    have hn : ¬T≤∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0 := by
      intro he
      exact hx (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,he⟩⟩)
    have he : (∑ H∈pencil x,weights S C c i H)=
        ∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0 := by
      rw [pencil,sum_filter]
      apply sum_congr rfl
      intro H _
      simp only [_root_.OAI.SharpLogRamsey.Incidence.incident_iff_submodule]
    rw [he]
    exact lt_of_not_ge hn

end
end SharpLogRamsey.PreparedVariance

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma own_empty_or_index (S : Finset A) (U : B→Finset A) (bs : List B) (x : A) :
    own S U bs x=∅ ∨ ∃ i : Fin bs.length,own S U bs x=indexedCell S U bs i := by
  rcases own_empty_or_cell S U bs x with he|he
  · exact Or.inl he
  · right
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
    have hil : i.val<bs.length := by simpa only [cells_length] using i.isLt
    refine ⟨⟨i.val,hil⟩,?_⟩
    rw [indexedCell_eq]
    exact hi.symm

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical PreparedVariance RegularPencils GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedGeometry.flat_JoinedPreparedGeometry_2
local instance flat_JoinedPreparedGeometry_3_r84a94b_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
lemma not_bad (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (H : Projectivization K (Module.Dual K V)) (hH : H∉badHyperplanes S U bs c)
    (x : Projectivization K V) :
    |mass S c H-1|≤1/10 ∧
    |mass (own S U bs x) c H-((own S U bs x).card:ℝ)/(S.card:ℝ)|≤1/50 := by
  have hh : ¬(1/10 < |mass S c H-1| ∨ ∃ i : Fin bs.length,
      1/50 < |mass (indexedCell S U bs i) c H-((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)|) := by
    simpa only [badHyperplanes,exceptional,mem_filter,mem_univ,true_and] using hH
  obtain ⟨hl,hc⟩ := not_or.mp hh
  refine ⟨le_of_not_gt hl,?_⟩
  rcases own_empty_or_index S U bs x with he|⟨i,he⟩
  · simp [he,mass]
  · rw [he]
    exact le_of_not_gt (fun hi => hc ⟨i,hi⟩)

omit [Finite K] [FiniteDimensional K V] in
lemma cell_sum_le (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) :
    (∑ i : Fin bs.length,(indexedCell S U bs i).card)≤S.card := by
  rw [indexedCell_sum]
  exact card_le_card (removed_subset S U bs)

lemma pencil_exception_count (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (x : Projectivization K V) :
    (∑ H∈pencil x,weights S (indexedCell S U bs) c (some none) H)=
      ((pencil x∩badHyperplanes S U bs c).card:ℝ) := by
  simp only [weights,←sum_filter]
  change (∑ H∈(pencil x).filter (fun H => H∈badHyperplanes S U bs c),(1:ℝ))=_
  rw [filter_mem_eq_inter]
  simp

theorem regular_preparation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) (hcsmall : (c:ℝ)≤1/100)
    (hcell : ∀ i : Fin bs.length,((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)≤1/25)
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤T/2) :
    let E := badHyperplanes S U bs c
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*(T/2)^2≤10408*(Nat.card K:ℝ)^(2*n+4)/(S.card:ℝ) ∧
      (E.card:ℝ)≤10400*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) ∧
      (∑ H∈E,mass S c H)≤20804*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) ∧
      (∀ x,((own S U bs x).card:ℝ)/(S.card:ℝ)≤1/25) ∧
      ∀ x,x∉D →
        ((pencil x∩E).card:ℝ)<T ∧
        (∀ H∈pencil x\E,
          3/4≤outsideMass S (own S U bs x) x c H ∧
          outsideMass S (own S U bs x) x c H≤2 ∧
          |outsideMass S (own S U bs x) x c H-
            (1-((own S U bs x).card:ℝ)/(S.card:ℝ))|≤13/100) ∧
        (∑ H∈pencil x\E,(outsideMass S (own S U bs x) x c H-
          (1-((own S U bs x).card:ℝ)/(S.card:ℝ)))^2)≤
            3*(T+T+((pencil x\E).card:ℝ)*(c:ℝ)^2) := by
  dsimp only
  obtain ⟨D,hD,hr⟩ := exists_regular hdim S hS (indexedCell S U bs) (cell_sum_le S U bs) c hc T hT hmean
  have he := actual_exceptions hdim S hS (indexedCell S U bs) (cell_sum_le S U bs) c hc
  dsimp only at he
  have hf (x : Projectivization K V) : ((own S U bs x).card:ℝ)/(S.card:ℝ)≤1/25 := by
    rcases own_empty_or_index S U bs x with he|⟨i,he⟩
    · simp [he]
    · rw [he]; exact hcell i
  refine ⟨D,hD,he.2.2.1,he.2.2.2,hf,?_⟩
  intro x hx
  have hO : own S U bs x⊆S := (own_subset_removed S U bs x).trans (removed_subset S U bs)
  have hfull : (∑ H∈pencil x,min 1 ((mass S c H-1)^2))≤T := (hr x hx none).le
  have hown : (∑ H∈pencil x,min 1 ((mass (own S U bs x) c H-
      ((own S U bs x).card:ℝ)/(S.card:ℝ))^2))≤T := by
    rcases own_empty_or_index S U bs x with hh|⟨i,hh⟩
    · simpa [hh,mass] using hT
    · rw [hh]
      exact (hr x hx (some (some i))).le
  have hn (H : Projectivization K (Module.Dual K V)) (hH : H∈pencil x\badHyperplanes S U bs c) :=
    not_bad S U bs c H (mem_sdiff.mp hH).2 x
  refine ⟨?_,?_,?_⟩
  · rw [←pencil_exception_count]
    exact hr x hx (some none)
  · intro H hH
    exact typical_point S _ hO x c H _ hcsmall (by positivity) (hf x) (hn H hH).1 (hn H hH).2
  · exact typical_squares S _ hO x c _ sdiff_subset _ T T
      (fun H hH => (hn H hH).1) (fun H hH => (hn H hH).2) hfull hown

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedShortRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow GreedyPreparation Real
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPreparedShortRow_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PreparedDescription.flat_JoinedPreparedShortRow_4
lemma good_mono (S : Finset (Projectivization K V))
    (plane : B→Finset (Projectivization K V)) (bs : List (B×ℕ))
    {L cap cap' size size' : ℝ} {R : ℕ} {ω : Fin R×Projectivization K V→ℕ}
    (hc : cap' ≤ cap) (hs : size ≤ size') (h : good S plane bs L cap size ω) :
    good S plane bs L cap' size' ω := by
  obtain ⟨z,hz,hcap,hsize⟩ := h
  exact ⟨z,hz,hc.trans hcap,hsize.trans hs⟩

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma acceptProb_mono {Ω : Type*} [Fintype Ω] (p : PublicTables.Law Ω)
    (A A' : Ω→Prop) (h : ∀ x,A x→A' x) :
    PublicTables.acceptProb p A≤PublicTables.acceptProb p A' := by
  unfold PublicTables.acceptProb PublicTables.accepted
  apply sum_le_sum
  intro x _
  by_cases hx : A x
  · simp only [hx,h x hx,ite_true]
    exact le_rfl
  · simp only [hx,ite_false]
    split_ifs <;> simp [p.nonneg x]

theorem short_proposal
    (n R p h M : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S₀ S U Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty)
    (hS₀ : S⊆S₀) (hSU : S⊆U) (hDa : Ds⊆Da)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (hf : ∀ x,((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)≤1/25)
    (σ P B₀ C b e W : ℝ) (hσ : 1≤σ) (hqexp : exp σ=(Nat.card K:ℝ))
    (hP : 100000000000000≤P) (hPu : P≤σ) (hPL : P=(L:ℝ)*R)
    (hBdef : B₀=(Nat.card K:ℝ)^(n+2)/(S.card:ℝ))
    (hb : 0≤b) (he : 0≤e) (hloss : b+e≤P/1000000)
    (hpP : 10000*σ≤(p:ℝ)*P)
    (hDs : (Ds.card:ℝ)≤S.card*exp (-P/200)+(S.card:ℝ)/10000)
    (hDaSize : (Da.card:ℝ)≤2*S.card+S.card*exp (5*P))
    (hN : 2*(Nat.card K:ℝ)*P≤S.card)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : exp (3*((L:ℝ)*R))≤B₀)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤e)
    (hW : 0≤W) (hWb : W≤20804*(Nat.card K:ℝ)*B₀)
    (hWsum : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : (Nat.card K:ℝ)*B₀*exp (-b-e)/8≤(E₀.card:ℝ)*exp (-e)/2)
    (herror : ∀ x,x∉Ds → exp (-(L:ℝ)*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤((Nat.card K:ℝ)*B₀*exp (-b-e)/8)/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ T a)
    (hM : 2*((R:ℝ)*S.card*(L*c:ℝ≥0))≤M) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(exp (-e)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (good S plane (sized S₀ plane bs) L ((S.card:ℝ)/2) (S.card*exp (6*P)))) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let z : ℝ := q*B₀*exp (-b-e)/8
  have hNpos : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hN1 : 1≤N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hq : 0<q := by rw [show q=exp σ from hqexp.symm]; exact exp_pos _
  have hBpos : 0<B₀ := by rw [hBdef]; positivity
  have hz : 0<z := by dsimp [z]; positivity
  have mean_eq : (R:ℝ)*S.card*(L*c:ℝ≥0)=q*P := by
    push_cast
    rw [hc,hPL]
    dsimp [q]
    field_simp
  have htotal : (Fintype.card (Projectivization K V):ℝ)≤2*exp (3*σ) := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V (show Module.finrank K V=(n+2)+1 by omega)]
    push_cast
    have hq2 : 2≤q := by
      have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
      dsimp [q]
      exact_mod_cast hh
    apply (Incidence.geom_sum_le_twice_pow q hq2 (n+2)).trans
    have hh : q^(n+2)≤q^3 := pow_le_pow_right₀ (by linarith : 1≤q) (by omega)
    have heq : q^3=exp (3*σ) := by rw [show q=exp σ from hqexp.symm,←exp_nat_mul]; norm_num
    rw [←heq]
    linarith
  have hlow := LearningScalar.short_row_lower hσ hP hPu hBpos hN1
    (Nat.cast_nonneg (Fintype.card (Projectivization K V))) htotal hW
    (by simpa only [hqexp] using hWb) hb he hloss hpP
  simp only [hqexp] at hlow
  have hgeom := geometric_proposal_probability n R p h M hn hdim S₀ S U Ds Da hS hS₀ hSU hDa
    plane bs E E₀ hE₀ hE₀E c L hc hf B₀ C e (1/1000) (1/1000) z W (N/100) N
    (by norm_num) (by norm_num) hz (by positivity) hNpos hC hL hR hp hpe hB hQ hα
    hsmall hWsum hZ herror T a hs ha hM
  dsimp only at hgeom hlow
  rw [←hPL,mean_eq] at hgeom
  have hcap : N/2≤N-(Ds.card:ℝ)-N/100-(10*((1/1000:ℝ)+1/1000))*N :=
    LearningScalar.row_capture hNpos.le (by linarith) hDs
  have hsize : 2*(q*P)+(Da.card:ℝ)+N+100*q^(n+3)/z≤N*exp (6*P) := by
    dsimp [z]
    rw [hBdef]
    have hh := LearningScalar.row_size hNpos hq (by linarith : 100000≤P)
      (by linarith : b+e≤P) hN hDaSize (n+2)
    convert hh using 1 <;> first | rfl | ring
  rw [show -P*(1/1000:ℝ)= -P/1000 by ring] at hgeom
  refine le_trans ?_ (le_trans hgeom ?_)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hlow
  · apply acceptProb_mono
    intro ω hω
    exact ⟨hω.1,hω.2.1,good_mono S plane (sized S₀ plane bs) hcap hsize hω.2.2⟩

end
end SharpLogRamsey.PreparedDescription

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedSparse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical GreedyPreparation
open scoped BigOperators Classical NNReal
noncomputable section

lemma half_small {α : Type*} (T : Finset α) (w : α→ℝ) (τ : ℝ)
    (hτ : 0<τ) (hw : ∀ x∈T,0≤w x) (hm : (∑ x∈T,w x)≤τ*T.card) :
    (T.card:ℝ)/2≤((T.filter (fun x => w x≤2*τ)).card:ℝ) := by
  let A := T.filter (fun x => w x≤2*τ)
  let B := T\A
  have hb : ∀ x∈B,2*τ≤w x := by
    intro x hx
    have hh := mem_sdiff.mp hx
    exact (lt_of_not_ge (fun he => hh.2 (mem_filter.mpr ⟨hh.1,he⟩))).le
  have hsum : 2*τ*(B.card:ℝ)≤∑ x∈T,w x := by
    calc
      _ = ∑ x∈B,2*τ := by simp [mul_comm]
      _ ≤ ∑ x∈B,w x := sum_le_sum hb
      _ ≤ ∑ x∈T,w x := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x hx _ => hw x hx)
  have hc : B.card+A.card=T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have hc' : (B.card:ℝ)+(A.card:ℝ)=T.card := by exact_mod_cast hc
  change (T.card:ℝ)/2≤(A.card:ℝ)
  nlinarith [hsum.trans hm]

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPreparedSparse_3_r84a94b_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
theorem sparse_training (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (T : Finset (Projectivization K (Module.Dual K V))) (hT : T.Nonempty)
    (τ : ℝ) (hτ : 0<τ) (hτsmall : 2*τ<9/10)
    (hSparse : (∑ H∈T,mass S c H)≤τ*T.card) :
    let E₀ := T.filter (fun H => mass S c H≤2*τ)
    E₀.Nonempty ∧ (T.card:ℝ)/2≤(E₀.card:ℝ) ∧
      E₀⊆badHyperplanes S U bs c ∧ ∀ H∈E₀,mass S c H≤2*τ := by
  dsimp only
  have hh := half_small T (mass S c) τ hτ (by intro H _; unfold mass; positivity) hSparse
  refine ⟨?_,hh,?_,?_⟩
  · apply card_pos.mp
    have hp : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
    have : (0:ℝ)<(T.filter (fun H => mass S c H≤2*τ)).card := lt_of_lt_of_le (by linarith) hh
    exact_mod_cast this
  · intro H hH
    have hb := (mem_filter.mp hH).2
    have habs : 1/10 < |mass S c H-1| := by
      rw [abs_of_neg (by linarith)]
      linarith
    simp only [badHyperplanes,RegularPencils.exceptional,mem_filter,mem_univ,true_and]
    exact Or.inl habs
  · intro H hH
    exact (mem_filter.mp hH).2

omit [Finite K] [FiniteDimensional K V] in

lemma sparse_training_exponent (S : Finset (Projectivization K V))
    (c L : ℝ≥0) (R : ℕ) (H : Projectivization K (Module.Dual K V))
    (τ : ℝ) (hH : mass S c H≤2*τ) :
    ((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤2*τ*((L:ℝ)*R) := by
  have hh := mul_le_mul_of_nonneg_left hH (show 0≤(L:ℝ)*R by positivity)
  unfold mass at hh
  simp only [inc,NNReal.coe_mul]
  nlinarith [hh]

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_UniversalTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

omit [Fintype Ω] in
lemma rows_card_le (n : ℕ) (z : Table Ω n) : (rows n z).card≤n := by
  induction n with
  | zero => simp [rows]
  | succ n ih => exact (card_insert_le _ _).trans (Nat.add_le_add_right (ih _) 1)

omit [Fintype Ω] in
lemma first_none_iff (A : Ω→Prop) (n : ℕ) (z : Table Ω n) :
    first A n z=none ↔ ∀ x∈rows n z,¬A x := by
  induction n with
  | zero => simp [first,rows]
  | succ n ih =>
    by_cases h : A z.1
    · simp [first,rows,h]
    · simpa [first,rows,h] using ih z.2

lemma missed_probability (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (∑ z,tableWeight p n z*(if first A n z=none then 1 else 0))=(1-acceptProb p A)^n := by
  have hh (z : Table Ω n) :
      (if first A n z=none then (1:ℝ) else 0)=1-outcome A (fun _ => 1) n z := by
    unfold outcome
    cases first A n z <;> simp
  simp_rw [hh,mul_sub,mul_one]
  rw [sum_sub_distrib,tableWeight_total]
  change 1-integral p A (fun _ => 1) n=_
  rw [production_probability]
  ring

lemma missing_exp (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (1-acceptProb p A)^n≤exp (-(n:ℝ)*acceptProb p A) := by
  have hh : 1-acceptProb p A≤exp (-acceptProb p A) := by
    have := add_one_le_exp (-acceptProb p A)
    linarith
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr (acceptProb_le_one p A)) hh n
  rw [←exp_nat_mul] at hp
  simpa only [mul_neg,neg_mul] using hp

theorem exists_universal (p : Law Ω) (A : ι→Ω→Prop) (n : ℕ)
    (h : (∑ i,(1-acceptProb p (A i))^n)<1) :
    ∃ z : Table Ω n,∀ i,∃ x∈rows n z,A i x := by
  by_contra! hn
  have hl (z : Table Ω n) :
      (1:ℝ)≤∑ i,if first (A i) n z=none then 1 else 0 := by
    obtain ⟨i,hi⟩ := hn z
    have hm : first (A i) n z=none := (first_none_iff _ _ _).mpr hi
    have hh := single_le_sum (f := fun i => if first (A i) n z=none then (1:ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa [hm] using hh
  have hh : (1:ℝ)≤∑ z,tableWeight p n z*(∑ i,if first (A i) n z=none then 1 else 0) := by
    calc
      _ = ∑ z,tableWeight p n z := (tableWeight_total p n).symm
      _ ≤ _ := by
        apply sum_le_sum
        intro z _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hl z) (tableWeight_nonneg p n z)
  simp_rw [mul_sum] at hh
  rw [sum_comm] at hh
  simp_rw [missed_probability] at hh
  linarith

theorem exists_cover (p : Law Ω) (A : ι→Ω→Prop) (a H : ℝ)
    (ha : 0≤a) (hcard : (Fintype.card ι:ℝ)≤exp H) (hH : H+1≤exp a)
    (hp : ∀ i,exp (-a)≤acceptProb p (A i)) :
    ∃ r : Finset Ω,r.card≤⌈exp (2*a)⌉₊ ∧ (∀ i,∃ x∈r,A i x) ∧
      log ((⌈exp (2*a)⌉₊:ℝ)+1)≤2*a+log 3 := by
  let n := ⌈exp (2*a)⌉₊
  have hN : exp (2*a)≤(n:ℝ) := Nat.le_ceil _
  have hl : (∑ i,(1-acceptProb p (A i))^n)<1 := by
    calc
      _ ≤ (∑ _i : ι,exp (-(n:ℝ)*exp (-a))) := by
        apply sum_le_sum
        intro i _
        apply (missing_exp p (A i) n).trans
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg n : (0:ℝ)≤n)
        nlinarith only [hh]
      _ = (Fintype.card ι:ℝ)*exp (-(n:ℝ)*exp (-a)) := by simp
      _ ≤ exp H*exp (-(n:ℝ)*exp (-a)) := by gcongr
      _ = exp (H-(n:ℝ)*exp (-a)) := by rw [←exp_add]; congr 1; ring
      _ ≤ exp (-1) := by
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hN (exp_pos (-a)).le
        have he : exp (2*a)*exp (-a)=exp a := by rw [←exp_add]; congr 1; ring
        rw [he] at hh
        linarith
      _ < 1 := exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨z,hz⟩ := exists_universal p A n hl
  refine ⟨rows n z,rows_card_le n z,hz,?_⟩
  have hn : (n:ℝ)<exp (2*a)+1 := Nat.ceil_lt_add_one (exp_pos _).le
  have he : 1≤exp (2*a) := one_le_exp_iff.mpr (by linarith)
  have hnp : (0:ℝ)<(n:ℝ)+1 := by positivity
  calc
    _ ≤ log (3*exp (2*a)) := by apply log_le_log hnp; linarith
    _ = _ := by rw [log_mul (by norm_num) (exp_ne_zero _),log_exp]; ring

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PublicDecoderCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι X : Type*} [Fintype Ω] [Fintype ι] [Fintype X]

omit [Fintype X] in

theorem decoder_cover (p : Law Ω) (A : ι→Ω→Prop) (a H cap size : ℝ)
    (Q : ℕ) (decode : Ω→Fin (Q+1)→Finset X) (support : ι→Finset X)
    (ha : 0≤a) (hcard : (Fintype.card ι:ℝ)≤exp H) (hH : H+1≤exp a)
    (hp : ∀ i,exp (-a)≤acceptProb p (A i))
    (hgood : ∀ i z,A i z → ∃ h,cap≤((support i)∩decode z h).card ∧
      ((decode z h).card:ℝ)≤ size) :
    ∃ m : Finset (Ω×Fin (Q+1)),
      m.card≤⌈exp (2*a)⌉₊*(Q+1) ∧
      (∀ z∈m,((decode z.1 z.2).card:ℝ)≤ size) ∧
      (∀ i,∃ z∈m,cap≤((support i)∩decode z.1 z.2).card) ∧
      log ((m.card:ℝ)+1)≤2*a+log 3+log ((Q:ℝ)+1) := by
  obtain ⟨r,hr,hits,hlen⟩ := exists_cover p A a H ha hcard hH hp
  let m := (r×ˢ(univ:Finset (Fin (Q+1)))).filter (fun z => ((decode z.1 z.2).card:ℝ)≤ size)
  have hm : m.card≤⌈exp (2*a)⌉₊*(Q+1) := by
    apply (card_filter_le _ _).trans
    rw [card_product,card_univ,Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hr
  refine ⟨m,hm,?_,?_,?_⟩
  · intro z hz
    exact (mem_filter.mp hz).2
  · intro i
    obtain ⟨z,hzr,hzi⟩ := hits i
    obtain ⟨h,hcap,hsize⟩ := hgood i z hzi
    exact ⟨(z,h),mem_filter.mpr ⟨mem_product.mpr ⟨hzr,mem_univ _⟩,hsize⟩,hcap⟩
  · have hh : (m.card:ℝ)+1≤((⌈exp (2*a)⌉₊:ℝ)+1)*((Q:ℝ)+1) := by
      have hh : (m.card:ℝ)≤(⌈exp (2*a)⌉₊:ℝ)*((Q:ℝ)+1) := by exact_mod_cast hm
      nlinarith [(show (0:ℝ)≤Q by positivity)]
    calc
      _ ≤ log (((⌈exp (2*a)⌉₊:ℝ)+1)*((Q:ℝ)+1)) := log_le_log (by positivity) hh
      _ = log ((⌈exp (2*a)⌉₊:ℝ)+1)+log ((Q:ℝ)+1) := log_mul (by positivity) (by positivity)
      _ ≤ _ := by linarith only [hlen]

omit [Fintype Ω] [Fintype ι] [Fintype X] in
lemma sampling_exponent {n u : ℝ} (hn : 0<n) (hu : 0<u) (M : ℕ) (e : ℝ) :
    (n/u)^M*(exp (-e)/4)=exp (-((M:ℝ)*log (u/n)+e+log 4)) := by
  have hh : exp ((M:ℝ)*log (u/n)+e+log 4)=(u/n)^M*exp e*4 := by
    rw [exp_add,exp_add,exp_nat_mul,exp_log (div_pos hu hn),exp_log (by norm_num : (0:ℝ)<4)]
  rw [exp_neg,exp_neg,hh]
  simp only [div_pow]
  field_simp

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_RegularPreparationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical GreedyPreparation
open scoped BigOperators Classical NNReal
noncomputable section

lemma geometric_ratio_le (q : ℝ) (hq : 0<q) (j : ℕ) :
    (∑ i∈range j,q^i)/(∑ i∈range (j+1),q^i)≤ 1/q := by
  have he : q*(∑ i∈range j,q^i)+1=∑ i∈range (j+1),q^i := by
    exact geom_sum_succ.symm
  have hp : 0<∑ i∈range (j+1),q^i := by
    have hn : 0≤ ∑ i∈range j,q^i := sum_nonneg (fun i _ => pow_nonneg hq.le i)
    nlinarith
  apply (div_le_div_iff₀ hp hq).mpr
  linarith

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedGeometry.flat_JoinedRegularPreparationBounds_2
local instance flat_JoinedRegularPreparationBounds_3_r84a94b_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
theorem source_regular_preparation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) (hcsmall : (c:ℝ)≤ 1/100)
    (hcell : ∀ i : Fin bs.length,((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)≤ 1/25)
    (L : ℝ) (hL : 0≤ L) :
    let B := (Nat.card K:ℝ)^(n+2)/(S.card:ℝ)
    let E := badHyperplanes S U bs c
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)≤ (S.card:ℝ)/10000*Real.exp (-L/500) ∧
      (E.card:ℝ)≤ 10400*(Nat.card K:ℝ)*B ∧
      (∑ H∈E,mass S c H)≤ 20804*(Nat.card K:ℝ)*B ∧
      (∀ x,((own S U bs x).card:ℝ)/(S.card:ℝ)≤ 1/25) ∧
      ∀ x,x∉D →
        ((pencil x∩E).card:ℝ)<50000*B*Real.exp (L/1000) ∧
        (∀ H∈pencil x\E,
          3/4≤ outsideMass S (own S U bs x) x c H ∧
          outsideMass S (own S U bs x) x c H≤ 2 ∧
          |outsideMass S (own S U bs x) x c H-
            (1-((own S U bs x).card:ℝ)/(S.card:ℝ))|≤ 13/100) ∧
        (∑ H∈pencil x\E,(outsideMass S (own S U bs x) x c H-
          (1-((own S U bs x).card:ℝ)/(S.card:ℝ)))^2)≤ 400000*B*Real.exp (L/1000) := by
  let q : ℝ := Nat.card K
  let s : ℝ := S.card
  let B : ℝ := q^(n+2)/s
  let e : ℝ := Real.exp (L/1000)
  have hq : 2≤ q := by
    change (2:ℝ)≤ Nat.card K
    have hh : 2≤ Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    exact_mod_cast hh
  have hq0 : 0<q := by linarith
  have hs : 0 < s := by
    change (0:ℝ)<S.card
    exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  have he : 1≤ e := Real.one_le_exp (by positivity)
  have he0 : 0<e := by linarith
  have hbpow : q^(n+3)/s=q*B := by dsimp [B]; rw [show n+3=n+2+1 by omega,pow_succ]; ring
  have hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤ (50000*B*e)/2 := by
    change (∑ k∈range (n+2),q^k)/(∑ k∈range (n+3),q^k)*(10408*(q^(n+3)/s))≤ _
    rw [hbpow]
    have hr : (∑ k∈range (n+2),q^k)/(∑ k∈range (n+3),q^k)≤ 1/q := by
      simpa only [show n+2+1=n+3 by omega] using geometric_ratio_le q hq0 (n+2)
    have hh := mul_le_mul_of_nonneg_right hr (show 0≤ 10408*(q*B) by positivity)
    have heq : 1/q*(10408*(q*B))=10408*B := by field_simp
    rw [heq] at hh
    nlinarith [mul_le_mul_of_nonneg_left he hB.le]
  obtain ⟨D,hD,hE,hW,hf,hr⟩ := regular_preparation hdim S hS U bs c hc hcsmall hcell
    (50000*B*e) (by positivity) hmean
  refine ⟨D,?_,?_,?_,hf,?_⟩
  · have heq : q^(2*n+4)/s=B^2*s := by
      dsimp [B]
      field_simp
      ring
    change (D.card:ℝ)*(50000*B*e/2)^2≤ 10408*q^(2*n+4)/s at hD
    have hdRewrite : 10408*q^(2*n+4)/s=10408*(B^2*s) := by rw [mul_div_assoc,heq]
    rw [hdRewrite] at hD
    have hd : (D.card:ℝ)*e^2≤ s/10000 := by
      have hh : (D.card:ℝ)*e^2*(625000000*B^2)≤ (s/10000)*(625000000*B^2) := by
        nlinarith [mul_nonneg (sq_nonneg B) hs.le]
      exact (mul_le_mul_iff_left₀ (by positivity : 0<625000000*B^2)).mp hh
    have hexp : Real.exp (-L/500)*e^2=1 := by
      dsimp [e]
      rw [←Real.exp_nat_mul,←Real.exp_add]
      norm_num only [Nat.cast_ofNat]
      rw [show -L/500+2*(L/1000)=0 by ring,Real.exp_zero]
    have hmul := mul_le_mul_of_nonneg_left hd (Real.exp_pos (-L/500)).le
    change (D.card:ℝ)≤ s/10000*Real.exp (-L/500)
    nlinarith [hexp]
  · change (badHyperplanes S U bs c).card≤ 10400*q*B
    change ((badHyperplanes S U bs c).card:ℝ)≤ 10400*(q^(n+3)/s) at hE
    rw [hbpow] at hE
    nlinarith only [hE]
  · change (∑ H∈badHyperplanes S U bs c,mass S c H)≤ 20804*q*B
    change (∑ H∈badHyperplanes S U bs c,mass S c H)≤ 20804*(q^(n+3)/s) at hW
    rw [hbpow] at hW
    nlinarith only [hW]
  · intro x hx
    obtain ⟨hpc,htyp,hsq⟩ := hr x hx
    refine ⟨hpc,htyp,hsq.trans ?_⟩
    have hc' : (c:ℝ)=q/s := hc
    have hcard : ((pencil x\badHyperplanes S U bs c).card:ℝ)≤ 2*q^(n+1) := by
      have hle : ((pencil x\badHyperplanes S U bs c).card:ℝ)≤ (pencil x).card := by
        exact_mod_cast card_le_card sdiff_subset
      have hpcard : (pencil x).card=∑ i∈range (n+2),Nat.card K^i := by
        have hd : Module.finrank K V=(n+2)+1 := by omega
        have hh := Incidence.card_incident_dual hd x
        rw [Nat.card_eq_fintype_card] at hh
        simpa only [Incidence.incident_iff_submodule,Fintype.card_subtype,pencil] using hh
      rw [hpcard] at hle
      exact hle.trans (by simpa only [Nat.cast_sum,Nat.cast_pow] using
        Incidence.geom_sum_le_twice_pow q hq (n+1))
    have heq : 2*q^(n+1)*(c:ℝ)^2=2*B*(c:ℝ) := by
      rw [hc']
      dsimp [B]
      field_simp
      ring
    have hsmall : ((pencil x\badHyperplanes S U bs c).card:ℝ)*(c:ℝ)^2≤ B/50 := by
      have hh := mul_le_mul_of_nonneg_right hcard (sq_nonneg (c:ℝ))
      rw [heq] at hh
      have hh' := mul_le_mul_of_nonneg_left hcsmall (show 0≤ 2*B by positivity)
      linarith
    change 3*(50000*B*e+50000*B*e+_*(c:ℝ)^2)≤ 400000*B*e
    nlinarith [mul_le_mul_of_nonneg_left he hB.le]

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanePencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedProjectiveGeometry PreparedTypical
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma plane_neighbors_empty (hdim : Module.finrank K V=3)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ) (ha : 0<a)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (H : Projectivization K (Module.Dual K V)) (hH : H∈A) :
    largeNeighbors S x c a A H=∅ := by
  apply filter_eq_empty_iff.mpr
  rintro J hJ ⟨hne,hh⟩
  have he := overlap_plane_zero hdim S x c H J hne
    (mem_filter.mp (hA hH)).2 (mem_filter.mp (hA hJ)).2
  linarith

theorem plane_pencils (hdim : Module.finrank K V=3)
    (R p h : ℕ) (hp : 0<p)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (f B C V₀ : ℝ) (hB : 0≤B)
    (htyp : ∀ H∈A,3/4≤outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-f)|≤13/100)
    (hsq : (∑ H∈A,(outsideMass S O x c H-(1-f))^2)≤V₀)
    (hsqs : V₀≤C*B*Real.exp ((L:ℝ)/100))
    (hsqa : V₀≤B*Real.exp (((L:ℝ)*R)/100))
    (hcards : ((∑ i∈range 2,Nat.card K^i):ℝ)≤C*B^2)
    (hcarda : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B^2)
    (hdir : (1:ℝ)≤4*B)
    (hdiag : C*2^R≤Real.exp ((L:ℝ)*R/20))
    (hpow : (2*(L:ℝ)^2)^R≤Real.exp ((L:ℝ)*R/25))
    (hsum : C^2*Real.exp ((L:ℝ)/50)≤Real.exp ((L:ℝ)*R/20))
    (htwo : 2≤Real.exp ((L:ℝ)*R/20))
    (hcert : MomentBudgetBridge.certificateOverhead p 0 ((L:ℝ)*R)≤Real.exp (2*((L:ℝ)*R)/25))
    (hshift : MomentBudgetBridge.shiftOverhead p 0≤Real.exp (2*((L:ℝ)*R)/25))
    (hpb : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hps : 2*(p:ℝ)+3≤Real.exp (((L:ℝ)*R)/10))
    (hh : 0<h) (hhs : h≤(R/2)/400) (hhe : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2) :
    SecondPencil 2 R S O x c L A f B C (∅ : Finset Unit) (fun _ => 0) ∧
    HighPencil 2 R p h S O x c L A f B (∅ : Finset Unit) (fun _ => 0) := by
  have hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J → False := by
    intro H hH J hJ hne hh
    have he := overlap_plane_zero hdim (S\(O∪{x})) x c H J hne
      (mem_filter.mp (hA hH)).2 (mem_filter.mp (hA hJ)).2
    linarith
  constructor
  · refine ⟨(fun H hH => (htyp H hH).1),(fun H hH => (htyp H hH).2.1),
      ?_,hsq.trans hsqs,hcards,?_,?_,?_,hdiag,hpow,?_,htwo⟩
    · intro H hH
      exact (htyp H hH).2.2.trans (by norm_num)
    · simp
    · intro H hH J hJ hne hh
      exact (hcover H hH J hJ hne hh).elim
    · simp
    · simpa using hsum
  · refine ⟨(fun H hH => (htyp H hH).1),(fun H hH => (htyp H hH).2.1),
      (fun H hH => (htyp H hH).2.2),hsq.trans hsqa,hcarda,?_,?_,?_,?_,?_,?_,
      ?_,?_,hpb,hps,hh,hhs,hhe⟩
    · simpa using hdir
    · simp
    · intro H hH J hJ hne hh
      exact (hcover H hH J hJ hne hh).elim
    · simp
    · simp
    · intro H hH
      have ha : (0:ℝ)<1/(100*(p:ℝ)) := by positivity
      rw [plane_neighbors_empty hdim (S\(O∪{x})) x c _ ha A hA H hH]
      simp only [card_empty,Nat.cast_zero]
      positivity
    · simpa using hcert
    · simpa using hshift

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section

lemma scale_B {q s P : ℝ} (hq : 0<q) (hs : 0 < s) (hsmall : s^2≤2*q^3)
    (hP : 2*exp (6*P)≤q) : exp (3*P)≤q^2/s := by
  have hsq : s^2*(exp (3*P))^2≤q^4 := by
    have he : (exp (3*P))^2=exp (6*P) := by rw [←exp_nat_mul]; congr 1; ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hsmall (exp_pos (6*P)).le
    nlinarith only [hh, mul_nonneg (show 0≤q^3 by positivity) (sub_nonneg.mpr hP)]
  apply (le_div_iff₀ hs).mpr
  have hp : 0≤exp (3*P)*s := by positivity
  nlinarith [sq_nonneg (exp (3*P)*s-q^2)]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPlanarBudget_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
omit [Finite K] [FiniteDimensional K V] in
lemma sparse_mass (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (c : ℝ≥0) :
    (∑ H∈T,mass S c H)=(c:ℝ)*(Incidence.incidenceCount S T:ℝ) := by
  simp only [mass,Incidence.incidenceCount,Nat.cast_sum,mul_sum, Incidence.incident_iff_submodule]

lemma plane_pencil_budgets (hdim : Module.finrank K V=3)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (σ P B : ℝ) (R p h : ℕ) (hbud : Budget σ P L R p h) (hB : 0<B)
    (htyp : ∀ H∈A,3/4≤outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-((O.card:ℝ)/(S.card:ℝ)))|≤13/100)
    (hsq : (∑ H∈A,(outsideMass S O x c H-(1-((O.card:ℝ)/(S.card:ℝ))))^2)≤
      400000*B*exp ((L:ℝ)/1000))
    (hcards : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B^2) (hdir : (1:ℝ)≤4*B) :
    SecondPencil 2 R S O x c L A ((O.card:ℝ)/(S.card:ℝ)) B 400000 (∅ : Finset Unit) (fun _ => 0) ∧
    HighPencil 2 R p h S O x c L A ((O.card:ℝ)/(S.card:ℝ)) B (∅ : Finset Unit) (fun _ => 0) := by
    have hsqs : 400000*B*exp ((L:ℝ)/1000)≤400000*B*exp ((L:ℝ)/100) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact exp_le_exp.mpr (by nlinarith [L.coe_nonneg])
    have hsqa : 400000*B*exp ((L:ℝ)/1000)≤B*exp (P/100) := by
      have hh := mul_le_mul_of_nonneg_left hbud.variance hB.le
      nlinarith only [hh]
    have hcs : ((∑ i∈range 2,Nat.card K^i):ℝ)≤400000*B^2 := by
      nlinarith [sq_nonneg B]
    exact plane_pencils hdim R p h hbud.p_pos S O x c L A hA _ B 400000 _
      hB.le htyp hsq hsqs (by simpa only [←hbud.identity] using hsqa) hcs hcards hdir
      (by simpa only [←hbud.identity] using hbud.diag)
      (by simpa only [←hbud.identity] using hbud.pow)
      (by simpa only [←hbud.identity] using hbud.sum)
      (by simpa only [←hbud.identity] using hbud.two)
      (by simpa only [←hbud.identity] using hbud.cert)
      (by simpa only [←hbud.identity] using hbud.shift)
      (by simpa only [←hbud.identity] using hbud.pb)
      (by simpa only [←hbud.identity] using hbud.ps)
      hbud.h_pos hbud.h_small hbud.h_root

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma plane_error {q B L b e X : ℝ} (hq : 0<q) (hB : 0≤B) (hL : 0≤L)
    (hX : X≤50000*B*exp (L/1000))
    (herror : 50000*exp (-(95/100:ℝ)*L)≤exp (-b-e)/800) :
    exp (-L)*X≤(q*B*exp (-b-e)/8)/(100*q) := by
  calc
    _ ≤ exp (-L)*(50000*B*exp (L/1000)) := mul_le_mul_of_nonneg_left hX (exp_pos _).le
    _ = 50000*B*exp (-L+L/1000) := by rw [exp_add]; ring
    _ ≤ 50000*B*exp (-(95/100:ℝ)*L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact exp_le_exp.mpr (by linarith only [hL])
    _ ≤ (q*B*exp (-b-e)/8)/(100*q) := by
      have hh := mul_le_mul_of_nonneg_left herror hB
      have he : (q*B*exp (-b-e)/8)/(100*q)=B*exp (-b-e)/800 := by field_simp; ring
      rw [he]
      nlinarith only [hh]

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_PlanarScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Topology
noncomputable section

lemma even_order {σ P : ℝ} (hσ : 0<σ) (hP : 0<P) :
    ∃ p : ℕ,0<p ∧ Even p ∧ 10000*σ≤(p:ℝ)*P ∧ (p:ℝ)≤10000*σ/P+2 := by
  let p := 2*⌈5000*σ/P⌉₊
  have hn : 0≤5000*σ/P := by positivity
  have hl := Nat.le_ceil (5000*σ/P)
  have hu := Nat.ceil_lt_add_one hn
  have hp : (p:ℝ)=2*(⌈5000*σ/P⌉₊:ℝ) := by simp only [p,Nat.cast_mul,Nat.cast_ofNat]
  have hlo : 10000*σ≤(p:ℝ)*P := by
    have hh := mul_le_mul_of_nonneg_right hl hP.le
    have he : (5000*σ/P)*P=5000*σ := div_mul_cancel₀ _ hP.ne'
    rw [he] at hh
    rw [hp]
    nlinarith only [hh]
  refine ⟨p,?_,by dsimp [p]; exact even_two_mul _,hlo,?_⟩
  · have hpos : (0:ℝ)<p := by nlinarith only [hlo,hσ,hP]
    exact_mod_cast hpos
  · rw [hp]
    calc
      _ ≤ 2*(5000*σ/P+1) := (mul_lt_mul_of_pos_left hu (by norm_num : (0:ℝ)<2)).le
      _ = _ := by ring

lemma eventually_schedule {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      (R:ℝ)*exp (-(24/25:ℝ)*scaleL σ η D)≤1/10 := by
  have hh := ScaleSelection.eventually_polynomial_le_exp_rpow 40 (beta η) (9*beta η) (24/25)
    (by have := beta_pos hη; positivity) (by norm_num)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with σ hs hσ D R had
  have hR := R_bound hσ hη had
  have hL := (scale_bounds hσ hη had).1
  have he : 10*(R:ℝ)≤exp ((24/25:ℝ)*scaleL σ η D) := by
    calc
      _ ≤ 40*σ^beta η := by linarith
      _ ≤ exp ((24/25:ℝ)*σ^(9*beta η)) := hs
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right he (exp_pos (-(24/25:ℝ)*scaleL σ η D)).le
  have heq : exp ((24/25:ℝ)*scaleL σ η D)*exp (-(24/25:ℝ)*scaleL σ η D)=1 := by
    rw [←exp_add]; ring_nf; exact exp_zero
  rw [heq] at hm
  linarith

theorem eventually_budget {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∃ p h : ℕ,Budget σ (scaleP σ η D R) (Real.toNNReal (scaleL σ η D)) R p h := by
  filter_upwards [eventually_enumeration_budgets hη,
    eventually_pencil_scalar_budgets hη 400000,eventually_P_le_linear hη (1/12) (by norm_num),
    eventually_uniform_L hη (eventually_ge_atTop (100000000000000:ℝ)),
    eventually_uniform_R hη 400,eventually_schedule hη,eventually_ge_atTop (2:ℝ)]
    with σ he hp hu hl hr hs hσ D R had
  let L := scaleL σ η D
  let P := scaleP σ η D R
  have hL : 100000000000000≤L := hl D R had
  have hR : (400:ℝ)≤R := hr D R had
  have hL0 : 0≤L := by linarith
  have hLP : L≤P := by change L≤L*R; nlinarith
  have hP0 : 0<P := by linarith
  obtain ⟨p,hp0,hpe,hpl,hpu⟩ := even_order (by linarith : 0<σ) hP0
  obtain ⟨hLa,hcert,hshift,hpb,hps,h,hh,hR',hhs,hhr⟩ := he D R p 0 had hpu (by simpa only [Nat.cast_zero] using sq_nonneg σ)
  obtain ⟨hdiag,hpow,hsum,htwo,hvar⟩ := hp D R 0 had (by simpa only [Nat.cast_zero] using sq_nonneg σ)
  have hlu : (Real.toNNReal L:ℝ)=L := Real.coe_toNNReal _ hL0
  have hPu : P≤σ/12 := by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hu D R had
  have hB : 2*exp (6*P)≤exp σ := by
    have h2 : 2≤exp (σ-6*P) := by have := add_one_le_exp (σ-6*P); linarith
    calc
      _ ≤ exp (σ-6*P)*exp (6*P) := mul_le_mul_of_nonneg_right h2 (exp_pos _).le
      _ = _ := by rw [←exp_add]; congr 1; ring
  change ∃ p h : ℕ,Budget σ P (Real.toNNReal L) R p h
  refine ⟨p,h,?_⟩
  constructor
  · exact hσ
  · exact hL.trans hLP
  · linarith
  · exact hB
  · rw [hlu]; rfl
  · rw [hlu]; linarith
  · exact hR'
  · exact hp0
  · exact hpe
  · exact hpl
  · simpa only [hlu] using hs D R had
  · exact hdiag
  · simpa only [hlu] using hpow
  · simpa only [hlu,Nat.cast_zero,zero_mul,add_zero] using hsum
  · exact htwo
  · simpa only [hlu] using hvar
  · exact hcert
  · exact hshift
  · exact hpb
  · exact hps
  · exact hh
  · exact hhs
  · exact hhr

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPlanarGeometry_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarGeometry_3
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarGeometry_4
theorem preparation (hdim : Module.finrank K V=3)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hST : S.card≤T.card)
    (σ P : ℝ) (L c : ℝ≥0) (R p h : ℕ) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hcs : (c:ℝ)≤1/100) (hbud : Budget σ P L R p h)
    (hsp : (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K)) :
    let B := (Nat.card K:ℝ)^2/S.card
    let E := badHyperplanes S (fun _ : Unit => ∅) [] c
    ∃ Ds : Finset (Projectivization K V),
      (Ds.card:ℝ)≤(S.card:ℝ)/10000 ∧
      (∑ H∈E,mass S c H)≤20804*(Nat.card K:ℝ)*B ∧
      (∀ x,((own S (fun _ : Unit => ∅) [] x).card:ℝ)/(S.card:ℝ)≤1/25) ∧
      ∀ x,x∉Ds →
        ((pencil x∩E).card:ℝ)≤50000*B*exp ((L:ℝ)/1000) ∧
        SecondPencil 2 R S (own S (fun _ : Unit => ∅) [] x) x c L (pencil x\E)
          (((own S (fun _ : Unit => ∅) [] x).card:ℝ)/(S.card:ℝ)) B 400000 (∅ : Finset Unit) (fun _ => 0) ∧
        HighPencil 2 R p h S (own S (fun _ : Unit => ∅) [] x) x c L (pencil x\E)
          (((own S (fun _ : Unit => ∅) [] x).card:ℝ)/(S.card:ℝ)) B (∅ : Finset Unit) (fun _ => 0) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let B : ℝ := q^2/N
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : 2≤q := by
    have hh : 2≤Nat.card K := Finite.one_lt_card
    dsimp [q]; exact_mod_cast hh
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  have hsmall : N^2≤2*q^3 := Incidence.sparse_smaller_square (n:=0) hdim S T hST hsp
  obtain ⟨Ds,hDs,hE,hW,hown,hregular⟩ := source_regular_preparation (n:=0) hdim S hS
    (fun _ : Unit => ∅) [] c hc hcs (by intro i; exact Fin.elim0 i) L L.coe_nonneg
  have hDsN : (Ds.card:ℝ)≤N/10000 := by
    apply hDs.trans
    have hh : exp (-(L:ℝ)/500)≤1 := exp_le_one_iff.mpr (by nlinarith [L.coe_nonneg])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (show 0≤N/10000 by positivity)
  have hcards : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B^2 :=
    Incidence.sparse_retained_pencil (n:=0) hdim S S hS Subset.rfl T hST hsp
  have hdir : (1:ℝ)≤4*B := Incidence.scalar_direction_two q N hq2 hNs hsmall
  refine ⟨Ds,hDsN,hW,hown,?_⟩
  intro x hx
  obtain ⟨he,htyp,hsq⟩ := hregular x hx
  refine ⟨he.le,?_⟩
  exact plane_pencil_budgets hdim S _ x c L _ sdiff_subset σ P B R p h
    hbud hB htyp hsq hcards hdir

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarTraining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPlanarTraining_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarTraining_3
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarTraining_4
theorem training (hdim : Module.finrank K V=3)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S.card≤T.card)
    (σ P τ : ℝ) (R p h : ℕ) (L c : ℝ≥0)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hbud : Budget σ P L R p h) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hsparse : (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K)
    (hN : 100*(Nat.card K:ℝ)*P≤S.card) :
    let E₀ := T.filter (fun H => mass S c H≤2*τ)
    (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) ∧
    exp (3*P)≤(Nat.card K:ℝ)^2/S.card ∧ (c:ℝ)≤1/100 ∧
    E₀.Nonempty ∧ (T.card:ℝ)≤2*E₀.card ∧
    E₀⊆badHyperplanes S (fun _ : Unit => ∅) [] c ∧
    ∀ H∈E₀,mass S c H≤2*τ := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hsp : (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) := by
    apply hsparse.trans
    have hh := mul_le_mul_of_nonneg_right hτsmall (show 0≤(S.card:ℝ)*T.card by positivity)
    calc
      _ ≤ ((1/20:ℝ)*((S.card:ℝ)*T.card))/(Nat.card K:ℝ) :=
        div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hh) hq.le
      _ = _ := by ring
  have hsmall : N^2≤2*q^3 := Incidence.sparse_smaller_square (n:=0) hdim S T hST hsp
  have hBbig : exp (3*P)≤q^2/N := scale_B hq hNs hsmall (by simpa only [hqexp] using hbud.B)
  have hcsmall : (c:ℝ)≤1/100 := by
    rw [hc]
    apply (div_le_iff₀ hNs).mpr
    have hp : 1≤P := by linarith [hbud.large]
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0≤100*q by positivity)]
  have htrain : (∑ H∈T,mass S c H)≤τ*T.card := by
    rw [sparse_mass,hc]
    have hh := mul_le_mul_of_nonneg_left hsparse (show 0≤q/N by positivity)
    have he : (q/N)*(τ*(S.card:ℝ)*T.card/Nat.card K)=τ*T.card := by
      change (q/N)*(τ*N*T.card/q)=τ*T.card
      field_simp
    exact hh.trans_eq he
  obtain ⟨hE₀,hhalf,hE₀E,hsmallE⟩ := sparse_training S (fun _ : Unit => ∅) [] c T hT τ hτ
    (by linarith) htrain
  exact ⟨hsp,hBbig,hcsmall,hE₀,by linarith only [hhalf],hE₀E,hsmallE⟩

lemma training_size {q N t z : ℝ} (hN : 0<N) (hz : 0≤z) (b e : ℝ)
    (hprod : q^3*exp (-b)≤N*t) (hhalf : t≤2*z) :
    q*(q^2/N)*exp (-b-e)/8≤z*exp (-e)/2 := by
  have hTlow : q*(q^2/N)*exp (-b)≤t := by
    have he : q*(q^2/N)*exp (-b)=q^3*exp (-b)/N := by ring
    rw [he]
    apply (div_le_iff₀ hN).mpr
    simpa only [mul_comm] using hprod
  have he : exp (-b-e)=exp (-b)*exp (-e) := by
    simpa only [sub_eq_add_neg] using exp_add (-b) (-e)
  rw [he]
  have ht : q*(q^2/N)*exp (-b)≤2*z := hTlow.trans hhalf
  have hh := mul_le_mul_of_nonneg_right ht (exp_pos (-e)).le
  nlinarith only [hh,mul_nonneg hz (exp_pos (-e)).le]

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPlanarRow_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarRow_4
theorem short_proposal (hdim : Module.finrank K V=3)
    (S U : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hSU : S⊆U) (hST : S.card≤T.card)
    (σ P b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hbud : Budget σ P L R p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hproduct : (Nat.card K:ℝ)^3*exp (-b)≤(S.card:ℝ)*T.card)
    (hsparse : (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K)
    (hN : 100*(Nat.card K:ℝ)*P≤S.card)
    (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(exp (-2*P*τ)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (PreparedDescription.good S (fun _ : Unit => ∅) [] L ((S.card:ℝ)/2) (S.card*exp (6*P)))) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let B : ℝ := q^2/N
  let E := badHyperplanes S (fun _ : Unit => ∅) [] c
  let E₀ := T.filter (fun H => mass S c H≤2*τ)
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : 2≤q := by
    have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    dsimp [q]
    exact_mod_cast hh
  have hP : 0<P := by linarith [hbud.large]
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨hsp,hBbig,hcsmall,hE₀,hhalf,hE₀E,hsmallE⟩ := training hdim S T hS hT hST
    σ P τ R p h L c hqexp hc hbud hτ hτsmall hsparse hN
  obtain ⟨Ds,hDsN,hW,hown,hpencils⟩ := preparation hdim S T hS hST σ P L c R p h hc hcsmall hbud hsp
  have hZ := training_size hNs (show 0≤(E₀.card:ℝ) by positivity) b (2*P*τ)
    hproduct hhalf
  have hErr : ∀ x,x∉Ds → exp (-(L:ℝ)*(1-((own S (fun _ : Unit => ∅) [] x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤(q*B*exp (-b-2*P*τ)/8)/(100*q) := by
    intro x hx
    have hc := (hpencils x hx).1
    simp only [own,card_empty,Nat.cast_zero,zero_div,sub_zero,mul_one]
    exact plane_error hq hB.le L.coe_nonneg hc herror
  have hmean : (R:ℝ)*S.card*(L*c:ℝ≥0)=q*P := by
    push_cast
    rw [hc,hbud.identity]
    dsimp [q]
    field_simp
  have hQ : (10:ℝ)≤∑ i∈range 3,(Nat.card K:ℝ)^i := by
    have hq3 : 3≤q := by
      have hh := add_one_le_exp σ
      rw [hqexp] at hh
      linarith [hbud.sigma]
    simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one]
    nlinarith
  have hout := PreparedDescription.short_proposal 0 R p h M (by omega) hdim S S U Ds Ds hS
    Subset.rfl hSU Subset.rfl (fun _ : Unit => ∅) [] E E₀ hE₀ hE₀E c L hc hown
    σ P B 400000 b (2*P*τ) (20804*q*B) (by linarith [hbud.sigma]) hqexp
    hbud.large hbud.upper hbud.identity rfl hb (by positivity) hloss hbud.order
    (by change (Ds.card:ℝ)≤N*exp (-P/200)+N/10000; linarith [mul_nonneg hNs.le (exp_pos (-P/200)).le])
    (by change (Ds.card:ℝ)≤2*N+N*exp (5*P); nlinarith [mul_nonneg hNs.le (exp_pos (5*P)).le])
    (by nlinarith [hbud.large]) (by norm_num) hbud.Llarge hbud.Rlarge hbud.p_pos hbud.p_even
    (by simpa only [←hbud.identity] using hBbig) hQ hbud.sparseSchedules
    (fun H hH => by simpa only [←hbud.identity,mul_comm,mul_left_comm,mul_assoc] using
      sparse_training_exponent S c L R H τ (hsmallE H hH))
    (by positivity) le_rfl (by simpa only [mass,hc,inc] using hW) (by simpa only [neg_mul] using hZ) hErr
    (∅ : Finset Unit) (fun _ => 0) (fun x hx => (hpencils x hx).2.1) (fun x hx => (hpencils x hx).2.2)
    (by rw [hmean]; nlinarith only [hM])
  simp only [sized,neg_mul] at hout ⊢
  with_unfolding_all exact hout

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPlanarPublic_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarPublic_3
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarPublic_4
lemma input_card (U : Finset (Projectivization K V)) (N : ℕ) (b τ : ℝ) :
    (Fintype.card {S // Input U N b τ S}:ℝ)≤
      exp ((Fintype.card (Projectivization K V):ℝ)*log 2) := by
  have hh := Fintype.card_subtype_le (Input U N b τ)
  rw [Fintype.card_finset] at hh
  rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
  exact_mod_cast hh

lemma input_probability (hdim : Module.finrank K V=3)
    (U : Finset (Projectivization K V)) (N : ℕ) (hN0 : 0<N)
    (σ P b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/N)
    (hbud : Budget σ P L R p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hN : 100*(Nat.card K:ℝ)*P≤N) (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) (S : Finset (Projectivization K V))
    (hS : Input U N b τ S) :
    ((N:ℝ)/(U.card:ℝ))^M*(exp (-2*P*τ)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*N*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (PreparedDescription.good S (fun _ : Unit => ∅) [] L ((N:ℝ)/2) (N*exp (6*P)))) := by
  obtain ⟨hSU,hSN,T,hT,hST,hpr,hsp⟩ := hS
  have hSn : S.Nonempty := card_pos.mp (by omega)
  have hh := short_proposal hdim S U T hSn hT hSU hST σ P b τ L c R p h M hqexp
    (by simpa only [hSN] using hc) hbud hb hτ hτsmall hpr hsp
    (by simpa only [hSN] using hN) hloss herror hM
  simpa only [hSN] using hh

lemma input_decode (U : Finset (Projectivization K V)) (N : ℕ) (L P b τ : ℝ)
    {R M : ℕ} (S : Finset (Projectivization K V)) (hS : Input U N b τ S)
    (ω : (Fin R×Projectivization K V)→Fin (M+2))
    (hω : PreparedProposals.accepts (coordinateSupport S R) M
      (PreparedDescription.good S (fun _ : Unit => ∅) [] L ((N:ℝ)/2) (N*exp (6*P))) ω) :
    ∃ z,(N:ℝ)/2≤(S∩decode U N L ω z).card ∧
      ((decode U N L ω z).card:ℝ)≤N*exp (6*P) := by
  obtain ⟨z,hz,hcap,hsize⟩ := hω.2.2
  rw [hS.2.1] at hcap hsize
  refine ⟨⟨z,by omega⟩,?_,?_⟩
  · have he : S∩decode U N L ω ⟨z,by omega⟩=
        S∩PreparedDecoder.decode (fun _ : Unit => ∅) [] N z pencil inc L (Nat.card K) (fun x => (ω x:ℕ)) := by
      ext x
      simp only [decode,mem_inter]
      exact ⟨fun hh => ⟨hh.1,hh.2.2⟩,fun hh => ⟨hh.1,hS.1 hh.1,hh.2⟩⟩
    rw [he]
    exact hcap
  · exact (show ((decode U N L ω ⟨z,by omega⟩).card:ℝ)≤
      (PreparedDecoder.decode (fun _ : Unit => ∅) [] N z pencil inc L (Nat.card K) (fun x => (ω x:ℕ))).card
        by exact_mod_cast card_le_card inter_subset_right).trans hsize

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPlanarCover_1_r84a94b_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarCover_3
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarCover_4
theorem public_cover (hdim : Module.finrank K V=3)
    (U : Finset (Projectivization K V)) (N : ℕ) (hN0 : 0<N) (hNU : N≤U.card)
    (σ P b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/N)
    (hbud : Budget σ P L R p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hN : 100*(Nat.card K:ℝ)*P≤N) (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    let H := (Fintype.card (Projectivization K V):ℝ)*log 2
    let a := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4+log (H+1)
    ∃ messages : Finset (((Fin R×Projectivization K V)→Fin (M+2)) ×
        Fin (Fintype.card (Projectivization K (Module.Dual K V))+1)),
      (∀ z∈messages,((decode U N L z.1 z.2).card:ℝ)≤N*exp (6*P)) ∧
      (∀ S,Input U N b τ S → ∃ z∈messages,
        (N:ℝ)/2≤(S∩decode U N L z.1 z.2).card) ∧
      log ((messages.card:ℝ)+1)≤2*a+log 3+
        log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1) := by
  dsimp only
  let H := (Fintype.card (Projectivization K V):ℝ)*log 2
  let a₀ := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4
  let a := a₀+log (H+1)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN0
  have hUr : (0:ℝ)<U.card := hNr.trans_le (by exact_mod_cast hNU)
  have hHr : 0≤H := mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by norm_num))
  have hHP : 0<H+1 := by linarith
  have hP : 0≤P := le_trans (by norm_num) hbud.large
  have ha₀ : 0≤a₀ := by
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg ((le_div_iff₀ hNr).mpr (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU))))
      · positivity
    · exact log_nonneg (by norm_num)
  have ha : 0≤a := add_nonneg ha₀ (log_nonneg (by linarith))
  have hea : H+1≤exp a := by
    dsimp only [a]
    rw [exp_add,exp_log hHP]
    exact le_mul_of_one_le_left (le_of_lt hHP) (one_le_exp_iff.mpr ha₀)
  let Ω := (Fin R×Projectivization K V)→Fin (M+2)
  let ι := {S // Input U N b τ S}
  let law := PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*N*(L*c)) M
  let A : ι→Ω→Prop := fun i => PreparedProposals.accepts (coordinateSupport i.1 R) M
    (PreparedDescription.good i.1 (fun _ : Unit => ∅) [] L ((N:ℝ)/2) (N*exp (6*P)))
  have hprob : ∀ i,exp (-a)≤PublicTables.acceptProb law (A i) := by
    intro i
    have hh := input_probability hdim U N hN0 σ P b τ L c R p h M hqexp hc hbud hb hτ hτsmall hN hloss herror hM i.1 i.2
    have he := PublicTables.sampling_exponent hNr hUr M (2*P*τ)
    simp only [neg_mul] at hh
    rw [he] at hh
    apply le_trans _ hh
    apply exp_le_exp.mpr
    dsimp only [a,a₀]
    have hh' : 0≤log (H+1) := log_nonneg (by linarith)
    linarith
  obtain ⟨messages,_,hsize,hcap,hlen⟩ := PublicTables.decoder_cover law A a H
    ((N:ℝ)/2) (N*exp (6*P))
    (Fintype.card (Projectivization K (Module.Dual K V))) (decode U N L) (fun i : ι => i.1)
    ha (input_card U N b τ) hea hprob
    (fun i ω hω => input_decode U N L P b τ i.1 i.2 ω hω)
  exact ⟨messages,hsize,fun S hS => hcap ⟨S,hS⟩,hlen⟩

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Classical BigOperators Topology NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarDescription_3
lemma plane_card (hdim : Module.finrank K V=3) :
    (Fintype.card (Projectivization K V):ℝ)=1+Nat.card K+(Nat.card K:ℝ)^2 := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
  norm_num [sum_range_succ]

lemma plane_log_card (hdim : Module.finrank K V=3) :
    log ((Fintype.card (Projectivization K V):ℝ)+1)≤2*Nat.card K ∧
    log ((Fintype.card (Projectivization K V):ℝ)*log 2+1)≤2*Nat.card K := by
  let q : ℝ := Nat.card K
  have hq : 1≤q := by
    dsimp only [q]
    exact_mod_cast (show 1≤Nat.card K from Nat.card_pos (α:=K))
  have hQ : (Fintype.card (Projectivization K V):ℝ)+1≤(q+1)^2 := by
    rw [plane_card hdim]; dsimp [q] at *; nlinarith
  have hlog : log ((q+1)^2)≤2*q := by
    rw [log_pow]
    have hh := log_le_sub_one_of_pos (show 0<q+1 by linarith)
    norm_num only [Nat.cast_ofNat]
    linarith
  have hfirst := (log_le_log (by positivity) hQ).trans hlog
  refine ⟨hfirst,?_⟩
  apply le_trans _ hfirst
  apply log_le_log (by have := log_nonneg (by norm_num : (1:ℝ)≤2); positivity)
  have hh : log 2≤(1:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  nlinarith [show (0:ℝ)≤Fintype.card (Projectivization K V) by positivity]

lemma description_cost {q P d τ H Q : ℝ} {M : ℕ}
    (hq : 1≤q) (hP : 1≤P) (hd : 0≤d) (hτ : τ≤1)
    (hM : (M:ℝ)≤2*q*P+1) (hH : log (H+1)≤2*q) (hQ : log (Q+1)≤2*q) :
    2*((M:ℝ)*d+2*P*τ+log 4+log (H+1))+log 3+log (Q+1)≤
      200*q*P*(d+P) := by
  have hqP : 1≤q*P := one_le_mul_of_one_le_of_one_le hq hP
  have hM' : (M:ℝ)≤3*q*P := by nlinarith
  have hMd := mul_le_mul_of_nonneg_right hM' hd
  have hPt := mul_le_mul_of_nonneg_left hτ (show 0≤2*P by linarith)
  have hPq : P≤q*P := le_mul_of_one_le_left (by linarith) hq
  have hqP' : q≤q*P := le_mul_of_one_le_right (by linarith) hP
  have hlog4 : log 4≤(3:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4); linarith
  have hlog3 : log 3≤(2:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hbig : q*P≤q*P*P := le_mul_of_one_le_right (by positivity) hP
  have hpos : 0≤q*P*d := by positivity
  nlinarith

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Classical BigOperators Topology NNReal
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarUniform_2
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarUniform_3
theorem source_cover_uniform {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V], ∀ D R, Admissible σ η D R →
    exp σ=(Nat.card K:ℝ) → Module.finrank K V=3 →
    ∀ (U : Finset (Projectivization K V)) (n : ℕ) (b τ : ℝ),
    0<n → n≤U.card → 100*(Nat.card K:ℝ)*scaleP σ η D R≤n →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    let M := ⌈2*(Nat.card K:ℝ)*P⌉₊
    let H := (Fintype.card (Projectivization K V):ℝ)*log 2
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S,Input U n b τ S → ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤2*((M:ℝ)*log ((U.card:ℝ)/n)+2*P*τ+log 4+log (H+1))+log 3+
        log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1) := by
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [eventually_budget hη,
    eventually_training_loss hη C (1/1000000) (by linarith) (by norm_num),
    eventually_exceptional_training hη C (by linarith),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20)),
    eventually_ge_atTop (1:ℝ)] with σ hb hl he ht hσ
  intro K V _ _ _ _ _ D R had hex hdim U n b τ hn hnu hnlarge hb0 hbu hτ hτu
  obtain ⟨p,h,hbud⟩ := hb D R had
  let P := scaleP σ η D R
  let L := Real.toNNReal (scaleL σ η D)
  let c := Real.toNNReal ((Nat.card K:ℝ)/n)
  let M := ⌈2*(Nat.card K:ℝ)*P⌉₊
  have hL0 : 0≤ scaleL σ η D := (L_pos (by linarith) had).le
  have hLL : (L:ℝ)=scaleL σ η D := coe_toNNReal _ hL0
  have hc : (c:ℝ)=(Nat.card K:ℝ)/n := coe_toNNReal _ (by positivity)
  have hLP : scaleL σ η D≤P := by
    have hR : (1:ℝ)≤R := by exact_mod_cast (show 1≤R by have := hbud.Rlarge; omega)
    exact le_mul_of_one_le_right hL0 hR
  have hloss : b+2*P*τ≤P/1000000 := by
    have hh := hl D R had b τ hbu hτu
    dsimp [P]
    nlinarith
  have herr : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800 := by
    rw [hLL]
    exact he D R had b τ hbu hτu
  obtain ⟨messages,hsize,hcapture,hlen⟩ := public_cover hdim U n hn hnu σ P b τ L c R p h M
    hex hc hbud hb0 hτ (hτu.trans ht.le) hnlarge hloss herr (Nat.le_ceil _)
  refine ⟨messages.image (fun z => decode U n L z.1 z.2),?_,?_,?_⟩
  · intro W hW
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hW
    exact ⟨inter_subset_left,hsize z hz⟩
  · intro S hS
    obtain ⟨z,hz,hcap⟩ := hcapture S hS
    exact ⟨_,mem_image.mpr ⟨z,hz,rfl⟩,hcap⟩
  · apply le_trans _ hlen
    apply log_le_log (by positivity)
    have hc := card_image_le (s:=messages) (f:=fun z => decode U n L z.1 z.2)
    have hc' : (((messages.image (fun z => decode U n L z.1 z.2)).card):ℝ) ≤ messages.card := by
      exact_mod_cast hc
    linarith only [hc']

theorem full_source_cover_uniform_oai {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],∀ D R,Admissible σ η D R →
    exp σ=(Nat.card K:ℝ) → Module.finrank K V=3 →
    ∀ (U : Finset (Projectivization K V)) (n : ℕ) (b τ : ℝ),
    0<n → n≤U.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S,Input U n b τ S → ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤200*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+P) := by
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [source_cover_uniform hη C hC,
    eventually_uniform_L hη (eventually_ge_atTop (1:ℝ)),
    eventually_uniform_R hη 1,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with σ hcover hL hR ht
  intro K V _ _ _ _ _ D R had hex hdim U n b τ hn hnu hb hbu hτ hτu
  let P := scaleP σ η D R
  let q : ℝ := Nat.card K
  let d := log ((U.card:ℝ)/n)
  have hP : 1≤P := one_le_mul_of_one_le_of_one_le (hL D R had) (hR D R had)
  have hq : 1≤q := by
    dsimp only [q]
    exact_mod_cast (show 1≤Nat.card K from Nat.card_pos (α:=K))
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hnu' : (n:ℝ)≤U.card := by exact_mod_cast hnu
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn').mpr (by linarith))
  have hqP : 1≤q*P := one_le_mul_of_one_le_of_one_le hq hP
  by_cases hsmall : (n:ℝ)≤100*q*P
  · obtain ⟨hsize,hcapture,hlen⟩ := DescriptionEnumeration.public_cover U n hn hnu
    refine ⟨U.powersetCard n,?_,?_,?_⟩
    · intro W hW
      obtain ⟨hWU,hnW⟩ := hsize W hW
      refine ⟨hWU,?_⟩
      rw [hnW]
      exact le_mul_of_one_le_right (by positivity) (one_le_exp_iff.mpr (by linarith))
    · intro S hS
      obtain ⟨W,hW,he⟩ := hcapture S hS.1 hS.2.1
      refine ⟨W,hW,?_⟩
      rw [he,hS.2.1]
      linarith
    · apply hlen.trans
      have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤d+1 by linarith)
      have hb' := mul_le_mul_of_nonneg_left (show d+1≤d+P by linarith)
        (show 0≤100*q*P by positivity)
      have hlow : 1≤q*P*(d+P) := le_trans hqP (le_mul_of_one_le_right (by positivity) (by linarith))
      have hl : log 2≤(1:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
      change _≤200*q*P*(d+P)
      dsimp only [d] at hh hb' hlow
      nlinarith
  · obtain ⟨caps,hsize,hcapture,hlen⟩ := hcover K V D R had hex hdim U n b τ hn hnu
      (le_of_not_ge hsmall) hb hbu hτ hτu
    refine ⟨caps,hsize,hcapture,hlen.trans ?_⟩
    apply description_cost hq hP hd (hτu.trans ht.le) (Nat.ceil_lt_add_one (by positivity)).le
      (plane_log_card hdim).2
      (plane_log_card (V:=Module.Dual K V) (Subspace.dual_finrank_eq.trans hdim)).1

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform_oai := @OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform_oai
