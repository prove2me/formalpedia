-- Prove2me | solution 1 for ImpactInvesting.Portfolio.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T00:29:44.246984+00:00
-- url     : https://prove2.me/submissions/08991c02-d536-4e04-8b1b-64d72a8ef6f1

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
import Definitions.Def_ImpactInvesting_Portfolio_Setting

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory

namespace P6Aux

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

/-- The set of tuples whose sorting permutation is `σ`. -/
def sortSet (σ : Equiv.Perm (Fin N)) : Set (Fin N → ℝ) := {x | Tuple.sort x = σ}

lemma measurableSet_sortSet (σ : Equiv.Perm (Fin N)) : MeasurableSet (sortSet σ) := by
  have h : sortSet σ = {x : Fin N → ℝ | Monotone (x ∘ σ) ∧
      ∀ i j, i < j → x (σ i) = x (σ j) → σ i < σ j} := by
    ext x
    simp only [sortSet, Set.mem_setOf_eq]
    rw [eq_comm, Tuple.eq_sort_iff]
  have h1 : MeasurableSet {x : Fin N → ℝ | Monotone (x ∘ σ)} := by
    have : {x : Fin N → ℝ | Monotone (x ∘ σ)} =
        ⋂ i : Fin N, ⋂ j : Fin N, {x : Fin N → ℝ | i ≤ j → x (σ i) ≤ x (σ j)} := by
      ext x; simp [Monotone]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
    · simp [hij]
  have h2 : MeasurableSet
      {x : Fin N → ℝ | ∀ i j, i < j → x (σ i) = x (σ j) → σ i < σ j} := by
    have : {x : Fin N → ℝ | ∀ i j, i < j → x (σ i) = x (σ j) → σ i < σ j} =
        ⋂ i : Fin N, ⋂ j : Fin N, {x : Fin N → ℝ | i < j → x (σ i) = x (σ j) → σ i < σ j} := by
      ext x; simp
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hij, hs]
      · simp only [hij, hs, true_implies, imp_false]
        have hm : MeasurableSet {x : Fin N → ℝ | x (σ i) = x (σ j)} :=
          measurableSet_eq_fun (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))
        exact hm.compl
    · simp [hij]
  rw [h, Set.setOf_and]
  exact h1.inter h2

/-- Decomposition over the sorting permutation. -/
lemma sort_decomp (x : Fin N → ℝ) (f : Equiv.Perm (Fin N) → ℝ) :
    f (Tuple.sort x) = ∑ σ, (sortSet σ).indicator (fun _ => f σ) x := by
  rw [Finset.sum_eq_single (Tuple.sort x)]
  · simp [sortSet]
  · intro b _ hb
    simp only [Set.indicator, sortSet, Set.mem_setOf_eq]
    rw [if_neg (fun h => hb h.symm)]
  · intro h; exact absurd (Finset.mem_univ _) h

section Gauss

variable {P : Measure Ω} [IsProbabilityMeasure P] {X α : Fin N → Ω → ℝ} {σα ρ : ℝ}

open ImpactInvesting.Portfolio

/-- The noise `ε_k = α_k - ρ σα X_k`. -/
def eps (X α : Fin N → Ω → ℝ) (a : ℝ) (k : Fin N) : Ω → ℝ := fun ω => α k ω - a * X k ω

lemma memLp_X (h : IsA1 P X α σα ρ) (i : Fin N) : MemLp (X i) 2 P :=
  (h.gaussian i).fst.memLp_two

lemma memLp_α (h : IsA1 P X α σα ρ) (i : Fin N) : MemLp (α i) 2 P :=
  (h.gaussian i).snd.memLp_two

lemma memLp_eps (h : IsA1 P X α σα ρ) (a : ℝ) (i : Fin N) : MemLp (eps X α a i) 2 P :=
  (memLp_α h i).sub ((memLp_X h i).const_mul a)

lemma integral_eps (h : IsA1 P X α σα ρ) (a : ℝ) (i : Fin N) : P[eps X α a i] = 0 := by
  unfold eps
  rw [integral_sub ((memLp_α h i).integrable one_le_two)
    (((memLp_X h i).const_mul a).integrable one_le_two),
    integral_const_mul, h.mean_X, h.mean_α]
  ring

lemma indep_X_eps_of_ne (h : IsA1 P X α σα ρ) (a : ℝ) {i j : Fin N} (hij : i ≠ j) :
    IndepFun (X i) (eps X α a j) P := by
  have hp := h.indep.indepFun hij
  have := hp.comp (φ := fun p : ℝ × ℝ => p.1) (ψ := fun p : ℝ × ℝ => p.2 - a * p.1)
    measurable_fst (by fun_prop)
  exact this

lemma indep_eps_eps_of_ne (h : IsA1 P X α σα ρ) (a : ℝ) {i j : Fin N} (hij : i ≠ j) :
    IndepFun (eps X α a i) (eps X α a j) P := by
  have hp := h.indep.indepFun hij
  have := hp.comp (φ := fun p : ℝ × ℝ => p.2 - a * p.1) (ψ := fun p : ℝ × ℝ => p.2 - a * p.1)
    (by fun_prop) (by fun_prop)
  exact this

lemma cov_X_eps (h : IsA1 P X α σα ρ) (i j : Fin N) :
    cov[X i, eps X α (ρ * σα) j; P] = 0 := by
  by_cases hij : i = j
  · subst hij
    unfold eps
    rw [covariance_fun_sub_right (memLp_X h i) (memLp_α h i) ((memLp_X h i).const_mul _),
      covariance_const_mul_right, covariance_self (memLp_X h i).aemeasurable, h.var_X,
      h.cov_Xα]
    ring
  · exact (indep_X_eps_of_ne h _ hij).covariance_eq_zero (memLp_X h i) (memLp_eps h _ j)

lemma cov_eps_eps (h : IsA1 P X α σα ρ) (i j : Fin N) :
    cov[eps X α (ρ * σα) i, eps X α (ρ * σα) j; P] =
      if i = j then σα ^ 2 * (1 - ρ ^ 2) else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hX := memLp_X h i
    have hα := memLp_α h i
    have hXa := hX.const_mul (ρ * σα)
    unfold eps
    rw [covariance_fun_sub_left (Z := fun ω => α i ω - ρ * σα * X i ω) hα hXa (hα.sub hXa), covariance_fun_sub_right hα hα hXa,
      covariance_fun_sub_right hXa hα hXa, covariance_const_mul_left, covariance_const_mul_left,
      covariance_const_mul_right, covariance_const_mul_right,
      covariance_self hα.aemeasurable, covariance_self hX.aemeasurable, covariance_comm (α i),
      h.var_X, h.var_α, h.cov_Xα]
    ring
  · rw [if_neg hij]
    exact (indep_eps_eps_of_ne h _ hij).covariance_eq_zero (memLp_eps h _ i) (memLp_eps h _ j)

/-- The joint law of `(X, ε)` is Gaussian. -/
lemma gaussian_X_eps (h : IsA1 P X α σα ρ) (a : ℝ) :
    HasGaussianLaw (fun ω => (fun i => X i ω, fun j => eps X α a j ω)) P := by
  have hZ : HasGaussianLaw (fun ω i => (X i ω, α i ω)) P :=
    iIndepFun.hasGaussianLaw (X := fun i ω => (X i ω, α i ω)) h.gaussian h.indep
  let L₁ : (Fin N → ℝ × ℝ) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi fun i => (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.proj i)
  let L₂ : (Fin N → ℝ × ℝ) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi fun i => (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.proj i) - a • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.proj i)
  have := hZ.map_fun (L₁.prod L₂)
  have e : (fun ω => (fun i => X i ω, fun j => eps X α a j ω)) =
      fun ω => (L₁.prod L₂) (fun i => (X i ω, α i ω)) := by
    funext ω
    simp [L₁, L₂, eps]
  rw [e]
  exact this

lemma indep_Xv_epsv (h : IsA1 P X α σα ρ) :
    IndepFun (fun ω i => X i ω) (fun ω j => eps X α (ρ * σα) j ω) P :=
  (gaussian_X_eps h _).indepFun_of_covariance_eval (cov_X_eps h)

end Gauss

lemma sort_decomp' (x : Fin N → ℝ) (f : Equiv.Perm (Fin N) → ℝ) :
    f (Tuple.sort x) = ∑ σ, (sortSet σ).indicator 1 x * f σ := by
  rw [sort_decomp x f]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hx : x ∈ sortSet σ <;> simp [hx]

lemma measurable_ind (σ : Equiv.Perm (Fin N)) :
    Measurable ((sortSet σ).indicator (1 : (Fin N → ℝ) → ℝ)) :=
  measurable_one.indicator (measurableSet_sortSet σ)

section Ord

variable {P : Measure Ω} [IsProbabilityMeasure P] {X α : Fin N → Ω → ℝ} {σα ρ : ℝ}

open ImpactInvesting.Portfolio

lemma aemeasurable_Xv (h : IsA1 P X α σα ρ) : AEMeasurable (fun ω i => X i ω) P :=
  aemeasurable_pi_lambda _ fun i => (memLp_X h i).aemeasurable

lemma memLp_ind_mul (h : IsA1 P X α σα ρ) (σ : Equiv.Perm (Fin N)) {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) :
    MemLp (fun ω => (sortSet σ).indicator 1 (fun i => X i ω) * Y ω) 2 P := by
  refine hY.of_le ?_ (ae_of_all _ fun ω => ?_)
  · exact (((measurable_ind σ).comp_aemeasurable (aemeasurable_Xv h)).aestronglyMeasurable).mul
      hY.1
  · simp only [Real.norm_eq_abs, abs_mul]
    by_cases hx : (fun i => X i ω) ∈ sortSet σ
    · simp [hx]
    · simp [hx]

/-- The noise attached to rank `i`. -/
noncomputable def ee (X α : Fin N → Ω → ℝ) (a : ℝ) (i : Fin N) : Ω → ℝ :=
  fun ω => eps X α a (Tuple.sort (fun k => X k ω) i) ω

lemma orderStatRV_decomp (i : Fin N) :
    orderStatRV X i = fun ω => ∑ σ, (sortSet σ).indicator 1 (fun k => X k ω) * X (σ i) ω := by
  funext ω
  exact sort_decomp' (fun k => X k ω) (fun σ => X (σ i) ω)

lemma ee_decomp (a : ℝ) (i : Fin N) :
    ee X α a i = fun ω => ∑ σ, (sortSet σ).indicator 1 (fun k => X k ω) * eps X α a (σ i) ω := by
  funext ω
  exact sort_decomp' (fun k => X k ω) (fun σ => eps X α a (σ i) ω)

lemma memLp_orderStatRV (h : IsA1 P X α σα ρ) (i : Fin N) : MemLp (orderStatRV X i) 2 P := by
  rw [orderStatRV_decomp]
  exact memLp_finsetSum _ fun σ _ => memLp_ind_mul h σ (memLp_X h (σ i))

lemma memLp_ee (h : IsA1 P X α σα ρ) (a : ℝ) (i : Fin N) : MemLp (ee X α a i) 2 P := by
  rw [ee_decomp]
  exact memLp_finsetSum _ fun σ _ => memLp_ind_mul h σ (memLp_eps h a (σ i))

lemma induced_eq (a : ℝ) (i : Fin N) :
    inducedOrderStatRV X α i = fun ω => a * orderStatRV X i ω + ee X α a i ω := by
  funext ω
  simp only [inducedOrderStatRV, inducedOrderStat, orderStatRV, orderStat, ee, eps]
  ring

/-- Integration against the independent pair `(X, ε)`, split over the sorting permutation. -/
lemma integral_split (h : IsA1 P X α σα ρ) (Φ Ψ : Equiv.Perm (Fin N) → (Fin N → ℝ) → ℝ)
    (hΦm : ∀ σ, Measurable (Φ σ)) (hΨm : ∀ σ, Measurable (Ψ σ))
    (hΦ : ∀ σ, Integrable (fun ω => Φ σ (fun i => X i ω)) P)
    (hΨ : ∀ σ, Integrable (fun ω => Ψ σ (fun j => eps X α (ρ * σα) j ω)) P) :
    ∫ ω, ∑ σ, Φ σ (fun i => X i ω) * Ψ σ (fun j => eps X α (ρ * σα) j ω) ∂P =
      ∑ σ, (∫ ω, Φ σ (fun i => X i ω) ∂P) * ∫ ω, Ψ σ (fun j => eps X α (ρ * σα) j ω) ∂P := by
  have hind := indep_Xv_epsv h
  have hind' : ∀ σ, IndepFun (fun ω => Φ σ (fun i => X i ω))
      (fun ω => Ψ σ (fun j => eps X α (ρ * σα) j ω)) P := fun σ =>
    hind.comp (hΦm σ) (hΨm σ)
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    exact (hind' σ).integral_fun_mul_eq_mul_integral (hΦ σ).1 (hΨ σ).1
  · intro σ _
    exact (hind' σ).integrable_mul (hΦ σ) (hΨ σ)

lemma sum_integral_ind (h : IsA1 P X α σα ρ) :
    ∑ σ, ∫ ω, (sortSet σ).indicator 1 (fun i => X i ω) ∂P = (1 : ℝ) := by
  have hint : ∀ σ : Equiv.Perm (Fin N), Integrable
      (fun ω => (sortSet σ).indicator 1 (fun i => X i ω) * (1 : ℝ)) P := fun σ =>
    (memLp_ind_mul h σ (memLp_const (1 : ℝ))).integrable one_le_two
  rw [← integral_finset_sum _ fun σ _ => by simpa using hint σ]
  have : (fun ω => ∑ σ, (sortSet σ).indicator (1 : (Fin N → ℝ) → ℝ) (fun i => X i ω)) =
      fun _ => (1 : ℝ) := by
    funext ω
    have := sort_decomp' (fun i => X i ω) (fun _ => (1 : ℝ))
    simpa using this.symm
  rw [this]
  simp

end Ord

section Moments

variable {P : Measure Ω} [IsProbabilityMeasure P] {X α : Fin N → Ω → ℝ} {σα ρ : ℝ}

open ImpactInvesting.Portfolio

lemma integral_ee (h : IsA1 P X α σα ρ) (j : Fin N) : P[ee X α (ρ * σα) j] = 0 := by
  calc P[ee X α (ρ * σα) j]
      = ∑ σ, (∫ ω, (sortSet σ).indicator 1 (fun i => X i ω) ∂P) *
          ∫ ω, eps X α (ρ * σα) (σ j) ω ∂P := by
        rw [ee_decomp]
        exact integral_split h (fun σ x => (sortSet σ).indicator 1 x) (fun σ y => y (σ j))
          (fun σ => measurable_ind σ) (fun σ => measurable_pi_apply _)
          (fun σ => by simpa using (memLp_ind_mul h σ (memLp_const (1 : ℝ))).integrable one_le_two)
          (fun σ => (memLp_eps h _ (σ j)).integrable one_le_two)
    _ = 0 := by
        refine Finset.sum_eq_zero fun σ _ => ?_
        have := integral_eps h (ρ * σα) (σ j)
        rw [this, mul_zero]

lemma integral_ord_ee (h : IsA1 P X α σα ρ) (i j : Fin N) :
    ∫ ω, orderStatRV X i ω * ee X α (ρ * σα) j ω ∂P = 0 := by
  have hpt : (fun ω => orderStatRV X i ω * ee X α (ρ * σα) j ω) = fun ω =>
      ∑ σ, ((sortSet σ).indicator 1 (fun k => X k ω) * X (σ i) ω) *
        eps X α (ρ * σα) (σ j) ω := by
    funext ω
    rw [show orderStatRV X i ω * ee X α (ρ * σα) j ω =
        (fun σ : Equiv.Perm (Fin N) => X (σ i) ω * eps X α (ρ * σα) (σ j) ω)
          (Tuple.sort (fun k => X k ω)) from rfl]
    refine (sort_decomp' (fun k => X k ω)
      (fun σ => X (σ i) ω * eps X α (ρ * σα) (σ j) ω)).trans ?_
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  calc ∫ ω, orderStatRV X i ω * ee X α (ρ * σα) j ω ∂P
      = ∑ σ, (∫ ω, (sortSet σ).indicator 1 (fun k => X k ω) * X (σ i) ω ∂P) *
          ∫ ω, eps X α (ρ * σα) (σ j) ω ∂P := by
        rw [hpt]
        exact integral_split h (fun σ x => (sortSet σ).indicator 1 x * x (σ i))
          (fun σ y => y (σ j))
          (fun σ => (measurable_ind σ).mul (measurable_pi_apply _))
          (fun σ => measurable_pi_apply _)
          (fun σ => (memLp_ind_mul h σ (memLp_X h (σ i))).integrable one_le_two)
          (fun σ => (memLp_eps h _ (σ j)).integrable one_le_two)
    _ = 0 := by
        refine Finset.sum_eq_zero fun σ _ => ?_
        have := integral_eps h (ρ * σα) (σ j)
        rw [this, mul_zero]

lemma integral_eps_mul (h : IsA1 P X α σα ρ) (k l : Fin N) :
    ∫ ω, eps X α (ρ * σα) k ω * eps X α (ρ * σα) l ω ∂P =
      if k = l then σα ^ 2 * (1 - ρ ^ 2) else 0 := by
  have := covariance_eq_sub (memLp_eps h (ρ * σα) k) (memLp_eps h (ρ * σα) l)
  rw [cov_eps_eps h, integral_eps h, integral_eps h] at this
  rw [this]
  simp

lemma integral_ee_ee (h : IsA1 P X α σα ρ) (i j : Fin N) :
    ∫ ω, ee X α (ρ * σα) i ω * ee X α (ρ * σα) j ω ∂P =
      if i = j then σα ^ 2 * (1 - ρ ^ 2) else 0 := by
  have hpt : (fun ω => ee X α (ρ * σα) i ω * ee X α (ρ * σα) j ω) = fun ω =>
      ∑ σ, (sortSet σ).indicator 1 (fun k => X k ω) *
        (eps X α (ρ * σα) (σ i) ω * eps X α (ρ * σα) (σ j) ω) := by
    funext ω
    exact sort_decomp' (fun k => X k ω)
      (fun σ => eps X α (ρ * σα) (σ i) ω * eps X α (ρ * σα) (σ j) ω)
  calc ∫ ω, ee X α (ρ * σα) i ω * ee X α (ρ * σα) j ω ∂P
      = ∑ σ, (∫ ω, (sortSet σ).indicator 1 (fun k => X k ω) ∂P) *
          ∫ ω, eps X α (ρ * σα) (σ i) ω * eps X α (ρ * σα) (σ j) ω ∂P := by
        rw [hpt]
        exact integral_split h (fun σ x => (sortSet σ).indicator 1 x)
          (fun σ y => y (σ i) * y (σ j))
          (fun σ => measurable_ind σ)
          (fun σ => (measurable_pi_apply _).mul (measurable_pi_apply _))
          (fun σ => by simpa using (memLp_ind_mul h σ (memLp_const (1 : ℝ))).integrable one_le_two)
          (fun σ => (memLp_eps h _ (σ i)).integrable_mul (memLp_eps h _ (σ j)))
    _ = ∑ σ, (∫ ω, (sortSet σ).indicator 1 (fun k => X k ω) ∂P) *
          (if i = j then σα ^ 2 * (1 - ρ ^ 2) else 0) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [integral_eps_mul h]
        simp only [σ.injective.eq_iff]
    _ = if i = j then σα ^ 2 * (1 - ρ ^ 2) else 0 := by
        rw [← Finset.sum_mul, sum_integral_ind h, one_mul]

lemma cov_ord_ee (h : IsA1 P X α σα ρ) (i j : Fin N) :
    cov[orderStatRV X i, ee X α (ρ * σα) j; P] = 0 := by
  rw [covariance_eq_sub (memLp_orderStatRV h i) (memLp_ee h _ j), integral_ee h]
  have := integral_ord_ee h i j
  simp only [Pi.mul_apply]
  rw [this]
  ring

lemma cov_ee_ee (h : IsA1 P X α σα ρ) (i j : Fin N) :
    cov[ee X α (ρ * σα) i, ee X α (ρ * σα) j; P] =
      if i = j then σα ^ 2 * (1 - ρ ^ 2) else 0 := by
  rw [covariance_eq_sub (memLp_ee h _ i) (memLp_ee h _ j), integral_ee h, integral_ee h]
  have := integral_ee_ee h i j
  simp only [Pi.mul_apply]
  rw [this]
  ring

lemma memLp_induced (h : IsA1 P X α σα ρ) (i : Fin N) :
    MemLp (inducedOrderStatRV X α i) 2 P := by
  rw [induced_eq (ρ * σα) i]
  exact ((memLp_orderStatRV h i).const_mul (ρ * σα)).add (memLp_ee h _ i)

lemma cov_induced (h : IsA1 P X α σα ρ) (i j : Fin N) :
    cov[inducedOrderStatRV X α i, inducedOrderStatRV X α j; P] =
      (ρ * σα) ^ 2 * cov[orderStatRV X i, orderStatRV X j; P] +
        if i = j then σα ^ 2 * (1 - ρ ^ 2) else 0 := by
  have hOi := (memLp_orderStatRV h i).const_mul (ρ * σα)
  have hOj := (memLp_orderStatRV h j).const_mul (ρ * σα)
  have hei := memLp_ee h (ρ * σα) i
  have hej := memLp_ee h (ρ * σα) j
  rw [induced_eq (ρ * σα) i, induced_eq (ρ * σα) j]
  change cov[(fun ω => ρ * σα * orderStatRV X i ω) + ee X α (ρ * σα) i,
    (fun ω => ρ * σα * orderStatRV X j ω) + ee X α (ρ * σα) j; P] = _
  rw [covariance_add_left hOi hei (hOj.add hej), covariance_add_right hOi hOj hej,
    covariance_add_right hei hOj hej, covariance_const_mul_left, covariance_const_mul_right,
    covariance_const_mul_right, covariance_comm (ee X α (ρ * σα) i),
    covariance_const_mul_left, cov_ord_ee h, cov_ord_ee h, cov_ee_ee h]
  ring

end Moments

/-- Variance of a finite linear combination as a double sum of covariances. -/
lemma var_lin {P : Measure Ω} [IsProbabilityMeasure P] (Z : Fin N → Ω → ℝ)
    (hZ : ∀ i, MemLp (Z i) 2 P) (S : Finset (Fin N)) (w : Fin N → ℝ) :
    Var[fun ω => ∑ i ∈ S, w i * Z i ω; P] = ∑ i ∈ S, ∑ j ∈ S, w i * w j * cov[Z i, Z j; P] := by
  rw [variance_fun_sum' (X := fun i ω => w i * Z i ω) fun i _ => (hZ i).const_mul (w i)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

lemma sym_sum (S : Finset (Fin N)) (f : Fin N → Fin N → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i ∈ S, ∑ j ∈ S, f i j = ∑ i ∈ S, f i i + 2 * ∑ i ∈ S, ∑ j ∈ S with i < j, f i j := by
  have hpt : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) +
      (if i = j then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, not_lt.2 hij.le]
    · subst hij; simp
    · simp [hij, hij.ne', not_lt.2 hij.le]
  have hA : ∑ i ∈ S, ∑ j ∈ S, f i j =
      ∑ i ∈ S, ∑ j ∈ S, (if i < j then f i j else 0) +
      ∑ i ∈ S, ∑ j ∈ S, (if j < i then f i j else 0) +
      ∑ i ∈ S, ∑ j ∈ S, (if i = j then f i j else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  have hB : ∑ i ∈ S, ∑ j ∈ S, (if j < i then f i j else 0) =
      ∑ i ∈ S, ∑ j ∈ S, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf]
  have hC : ∑ i ∈ S, ∑ j ∈ S, (if i = j then f i j else 0) = ∑ i ∈ S, f i i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq S i (fun j => f i j)]
    simp [hi]
  rw [hA, hB, hC]
  simp only [Finset.sum_filter]
  ring

end P6Aux

open MeasureTheory ProbabilityTheory ImpactInvesting.Portfolio in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X α : Fin N → Ω → ℝ) (σα ρ : ℝ) (hA1 : IsA1 P X α σα ρ) (hσα : 0 < σα)
    (hρ₁ : -1 < ρ) (hρ₂ : ρ < 1)
    (S : Finset (Fin N)) (w : Fin N → ℝ) (hw : ∑ i ∈ S, w i = 1) :
    P[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω] =
        ∑ i ∈ S, w i * P[inducedOrderStatRV X α i] ∧
    P[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω] =
        ρ * σα * ∑ i ∈ S, w i * P[orderStatRV X i] ∧
    Var[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω; P] =
        ∑ i ∈ S, w i ^ 2 * Var[inducedOrderStatRV X α i; P] +
          2 * ∑ i ∈ S, ∑ j ∈ S with i < j,
            w i * w j * cov[inducedOrderStatRV X α i, inducedOrderStatRV X α j; P] ∧
    Var[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω; P] =
        σα ^ 2 * ((1 - ρ ^ 2) * ∑ i ∈ S, w i ^ 2 +
          ρ ^ 2 * (∑ i ∈ S, w i ^ 2 * Var[orderStatRV X i; P] +
            2 * ∑ i ∈ S, ∑ j ∈ S with i < j,
              w i * w j * cov[orderStatRV X i, orderStatRV X j; P])) := by
  have hY : ∀ i, MemLp (inducedOrderStatRV X α i) 2 P := P6Aux.memLp_induced hA1
  have hO : ∀ i, MemLp (orderStatRV X i) 2 P := P6Aux.memLp_orderStatRV hA1
  have h1 : P[fun ω => ∑ i ∈ S, w i * inducedOrderStatRV X α i ω] =
      ∑ i ∈ S, w i * P[inducedOrderStatRV X α i] := by
    rw [integral_finset_sum _ fun i _ => ((hY i).integrable one_le_two).const_mul (w i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  have hEY : ∀ i, P[inducedOrderStatRV X α i] = ρ * σα * P[orderStatRV X i] := by
    intro i
    rw [P6Aux.induced_eq (ρ * σα) i,
      integral_add (((hO i).integrable one_le_two).const_mul _)
        ((P6Aux.memLp_ee hA1 _ i).integrable one_le_two),
      integral_const_mul, P6Aux.integral_ee hA1, add_zero]
  have hsymY : ∀ i j, w i * w j * cov[inducedOrderStatRV X α i, inducedOrderStatRV X α j; P] =
      w j * w i * cov[inducedOrderStatRV X α j, inducedOrderStatRV X α i; P] := by
    intro i j; rw [covariance_comm]; ring
  have hsymO : ∀ i j, w i * w j * cov[orderStatRV X i, orderStatRV X j; P] =
      w j * w i * cov[orderStatRV X j, orderStatRV X i; P] := by
    intro i j; rw [covariance_comm]; ring
  have hV := P6Aux.var_lin _ hY S w
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hEY]; ring
  · rw [hV, P6Aux.sym_sum S _ hsymY]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [covariance_self (hY i).aemeasurable]; ring
  · rw [hV]
    have hexp : ∀ i j, w i * w j * cov[inducedOrderStatRV X α i, inducedOrderStatRV X α j; P] =
        (ρ * σα) ^ 2 * (w i * w j * cov[orderStatRV X i, orderStatRV X j; P]) +
          (if i = j then σα ^ 2 * (1 - ρ ^ 2) * (w i * w j) else 0) := by
      intro i j
      rw [P6Aux.cov_induced hA1]
      split_ifs <;> ring
    simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [P6Aux.sym_sum S _ hsymO]
    have hd : ∑ i ∈ S, ∑ j ∈ S, (if i = j then σα ^ 2 * (1 - ρ ^ 2) * (w i * w j) else 0) =
        σα ^ 2 * (1 - ρ ^ 2) * ∑ i ∈ S, w i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_ite_eq S i (fun j => σα ^ 2 * (1 - ρ ^ 2) * (w i * w j)), if_pos hi]
      ring
    rw [hd]
    have hdiag : ∀ i, w i * w i * cov[orderStatRV X i, orderStatRV X i; P] =
        w i ^ 2 * Var[orderStatRV X i; P] := by
      intro i; rw [covariance_self (hO i).aemeasurable]; ring
    simp_rw [hdiag]
    ring
