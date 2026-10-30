-- Prove2me | solution 1 for JointParametricPricing.PSC.lemma_ec_1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:19:18.466272+00:00
-- url     : https://prove2.me/submissions/a3aedbe4-8bbe-44a1-bc08-4ff263f606aa

import Definitions.Def_JointParametricPricing_PSC_Exploration
import Mathlib

open scoped BigOperators

namespace S228JPP
open JointParametricPricing.PSC

noncomputable def one1 : Vec 1 := WithLp.toLp 2 (fun _ => (1:ℝ))

@[simp] lemma one1_apply (j : Fin 1) : one1 j = 1 := by simp [one1]

lemma line_apply (θ : Vec 1) (t : ℝ) : (θ + t • coordinate 0 : Vec 1) 0 = θ 0 + t := by
  simp [coordinate]

lemma vec1_ext {x y : Vec 1} (h : x 0 = y 0) : x = y := by
  ext j; fin_cases j; simpa using h

lemma norm_sq1 (z : Vec 1) : ‖z‖ ^ 2 = z 0 ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

lemma dist1 (z w : Vec 1) : dist z w = |z 0 - w 0| := by
  simp [EuclideanSpace.dist_eq, Real.dist_eq, Real.sqrt_sq_eq_abs]

noncomputable def dem (p : Vec 1) (θ : Vec 1) : Vec 1 :=
  (1/4 : ℝ) • (one1 - p) + (Real.sin (θ 0) / 16) • one1

@[simp] lemma dem_apply (p θ : Vec 1) (j : Fin 1) :
    dem p θ j = (1 - p j) / 4 + Real.sin (θ 0) / 16 := by
  simp [dem]; ring

noncomputable def inv (x : Vec 1) (_θ : Vec 1) : Vec 1 := one1 - (4:ℝ) • x

@[simp] lemma inv_apply (x θ : Vec 1) (j : Fin 1) : inv x θ j = 1 - 4 * x j := by
  simp [inv]

noncomputable def extD (a : Action 1) (θ : Vec 1) : Vec 1 :=
  WithLp.toLp 2 (fun j => (a j).elim 0 (fun p => (1 - p) / 4 + Real.sin (θ 0) / 16))

lemma revfun_eq (θ : Vec 1) :
    (fun y : Vec 1 => ∑ l, y l * inv y θ l) = fun y => y 0 * (1 - 4 * y 0) := by
  funext y; simp

lemma coordDeriv_rev (z : Vec 1) :
    coordDeriv (fun y : Vec 1 => y 0 * (1 - 4 * y 0)) z 0 = 1 - 8 * z 0 := by
  unfold coordDeriv
  have hf : (fun t : ℝ => (z + t • coordinate 0 : Vec 1) 0 * (1 - 4 * (z + t • coordinate 0 : Vec 1) 0))
      = fun t => (z 0 + t) * (1 - 4 * (z 0 + t)) := by
    funext t; rw [line_apply]
  rw [hf]
  have h1 : HasDerivAt (fun t : ℝ => z 0 + t) 1 0 := (hasDerivAt_id 0).const_add _
  have h2 : HasDerivAt (fun t : ℝ => (z 0 + t) * (1 - 4 * (z 0 + t)))
      (1 * (1 - 4 * (z 0 + 0)) + (z 0 + 0) * -(4 * 1)) 0 := h1.mul ((h1.const_mul 4).const_sub 1)
  rw [h2.deriv]; ring

lemma second_rev (x : Vec 1) :
    secondPartial (fun y : Vec 1 => y 0 * (1 - 4 * y 0)) x 0 0 = -8 := by
  unfold secondPartial
  have : (fun z : Vec 1 => coordDeriv (fun y : Vec 1 => y 0 * (1 - 4 * y 0)) z 0)
      = fun z => 1 - 8 * z 0 := by funext z; exact coordDeriv_rev z
  rw [this]; unfold coordDeriv
  have hf : (fun t : ℝ => 1 - 8 * (x + t • coordinate 0 : Vec 1) 0) = fun t => 1 - 8 * (x 0 + t) := by
    funext t; rw [line_apply]
  rw [hf]
  have h1 : HasDerivAt (fun t : ℝ => 1 - 8 * (x 0 + t)) (-(8 * 1)) 0 :=
    (((hasDerivAt_id 0).const_add _).const_mul 8).const_sub 1
  rw [h1.deriv]; ring


def box : Set (Vec 1) := {p | ∀ j, (0:ℝ) ≤ p j ∧ p j ≤ 1}

lemma box_iff (p : Vec 1) : (∀ j : Fin 1, (WithLp.toLp 2 (fun _ => (0:ℝ)) : Vec 1) j ≤ p j ∧
    p j ≤ (WithLp.toLp 2 (fun _ => (1:ℝ)) : Vec 1) j) ↔ 0 ≤ p 0 ∧ p 0 ≤ 1 := by
  simp [Fin.forall_fin_one]

lemma box_compact : IsCompact {p : Vec 1 | ∀ j : Fin 1, (WithLp.toLp 2 (fun _ => (0:ℝ)) : Vec 1) j ≤ p j ∧
    p j ≤ (WithLp.toLp 2 (fun _ => (1:ℝ)) : Vec 1) j} := by
  simp only [box_iff]
  apply Metric.isCompact_of_isClosed_isBounded
  · have hc : Continuous (fun z : Vec 1 => z 0) := by fun_prop
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun p hp => ?_⟩
    simp only [Set.mem_ofPred_eq] at hp
    rw [Metric.mem_closedBall, dist1]; simp; rw [abs_le]; constructor <;> linarith [hp.1, hp.2]

lemma mem0 {θ : Vec 1} (h : θ ∈ ({0} : Set (Vec 1))) : θ = 0 := h

noncomputable def M : Model 1 1 1 where
  n_pos := by norm_num
  m_pos := by norm_num
  q_pos := by norm_num
  T := 2
  T_pos := by norm_num
  A := fun _ _ => 1
  A_nonneg := by intros; norm_num
  C := fun _ => 1/8
  C_nonneg := by intros; norm_num
  lower := WithLp.toLp 2 (fun _ => 0)
  upper := WithLp.toLp 2 (fun _ => 1)
  price_nonempty := ⟨WithLp.toLp 2 (fun _ => 0), by simp⟩
  price_compact := box_compact
  Θ := {0}
  theta_compact := isCompact_singleton
  thetaStar := 0
  thetaStar_mem := rfl
  demand := dem
  inverse := inv
  omega := 4
  rbar := 1
  v := 8
  vbar := 8
  omega_pos := by norm_num
  rbar_pos := by norm_num
  v_pos := by norm_num
  vbar_pos := by norm_num
  demand_simplex := by
    intro θ hθ p hp
    rw [box_iff] at hp
    obtain rfl := mem0 hθ
    refine ⟨fun j => ?_, ?_⟩
    · fin_cases j; simp; linarith [hp.1, hp.2]
    · simp; linarith [hp.1, hp.2]
  rates_convex := by
    intro θ hθ
    obtain rfl := mem0 hθ
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩ a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hp hp'
    rw [box_iff] at hp hp'
    refine ⟨a • p + b • p', ?_, ?_⟩
    · show _
      simp only [Set.mem_ofPred_eq]; rw [box_iff]
      simp
      constructor <;> nlinarith [hp.1, hp.2, hp'.1, hp'.2]
    · obtain rfl : b = 1 - a := by linarith
      apply vec1_ext; simp; ring
  inverse_left := by
    intro θ hθ p hp
    obtain rfl := mem0 hθ
    apply vec1_ext; simp; ring
  inverse_right := by
    intro θ hθ x hx
    obtain rfl := mem0 hθ
    obtain ⟨p, hp, rfl⟩ := hx
    have : inv (dem p 0) 0 = p := by apply vec1_ext; simp; ring
    rw [this]; exact ⟨hp, rfl⟩
  demand_C2 := by
    intro θ hθ p hp
    unfold dem; fun_prop
  inverse_C2 := by
    intro θ hθ x hx
    unfold inv; fun_prop
  parameter_C1 := by
    intro p hp θ hθ
    unfold dem; fun_prop
  inverse_lipschitz := by
    intro θ hθ x hx y hy
    have : inv x θ - inv y θ = (4:ℝ) • (y - x) := by
      apply vec1_ext; simp; ring
    rw [this, norm_smul, norm_sub_rev]; simp
  parameter_lipschitz := by
    intro θ hθ p hp
    obtain rfl := mem0 hθ
    simp
  partial_lipschitz := by
    intro θ hθ p hp i j
    obtain rfl := mem0 hθ
    simp
  revenue_bound := by
    intro θ hθ x hx
    obtain rfl := mem0 hθ
    obtain ⟨p, hp, rfl⟩ := hx
    simp only [Set.mem_ofPred_eq] at hp
    rw [box_iff] at hp
    simp
    rw [← abs_mul, abs_le]; constructor <;> nlinarith [hp.1, hp.2]
  hessian_bounds := by
    intro θ hθ x hx z
    rw [revfun_eq]
    simp only [Fin.sum_univ_one, second_rev, norm_sq1]
    constructor <;> nlinarith
  extendedDemand := extD
  extended_agrees := by
    intro θ hθ p hp
    apply vec1_ext; simp [extD, ordinary]
  extended_simplex := by
    intro θ hθ a ha
    obtain rfl := mem0 hθ
    have key : 0 ≤ (extD a 0) 0 ∧ (extD a 0) 0 ≤ 1 := by
      simp only [extD, PiLp.toLp_apply]
      cases h : a 0 with
      | none => simp
      | some p =>
        have := ha 0 p h
        simp at this ⊢
        constructor <;> linarith [this.1, this.2]
    refine ⟨fun j => ?_, ?_⟩
    · fin_cases j; exact key.1
    · simpa [Fin.sum_univ_one] using key.2
  off_zero := by
    intro θ hθ a j hj
    simp [extD, hj]


noncomputable def x16 : Vec 1 := WithLp.toLp 2 (fun _ => (1/16 : ℝ))
noncomputable def p34 : Vec 1 := WithLp.toLp 2 (fun _ => (3/4 : ℝ))

lemma rates_eq (θ : Vec 1) : M.rates θ = (fun p => dem p θ) '' {p : Vec 1 | 0 ≤ p 0 ∧ p 0 ≤ 1} := by
  unfold Model.rates Model.prices
  simp only [M, box_iff]

lemma x16_mem (θ : M.Θ) : x16 ∈ (M.program θ).feasible := by
  have hθ : (θ : Vec 1) = 0 := θ.property
  refine ⟨?_, ?_⟩
  · show x16 ∈ M.rates θ
    rw [rates_eq, hθ]
    refine ⟨p34, ?_, ?_⟩
    · simp [p34]; norm_num
    · apply vec1_ext; simp [p34, x16]; norm_num
  · intro i
    simp [Model.program, CapacityProgram.load, M, x16]; norm_num

lemma hf : M.Feasible := fun θ => ⟨x16, x16_mem θ⟩

lemma rev_eq (θ x : Vec 1) : M.revenue θ x = x 0 * (1 - 4 * x 0) := by
  simp [Model.revenue, M]

lemma xstar (h : M.Feasible) (θ : M.Θ) : M.optimalRate h θ = x16 := by
  have hθ : (θ : Vec 1) = 0 := θ.property
  have spec := CapacityProgram.optimum_spec (M.program θ) (M.rates_compact θ) (h θ)
    (M.revenue_continuous θ)
  set x := M.optimalRate h θ with hx
  have h1 : x ∈ (M.program θ).feasible := spec.1
  have h2 := spec.2 x16 (x16_mem θ)
  change M.revenue θ x16 ≤ M.revenue θ x at h2
  rw [rev_eq, rev_eq] at h2
  obtain ⟨hd, hl⟩ := h1
  have hl0 := hl 0
  simp [Model.program, CapacityProgram.load, M] at hl0
  change x ∈ M.rates θ at hd
  rw [rates_eq, hθ] at hd
  obtain ⟨p, hp, hpx⟩ := hd
  have hx0 : x 0 = (1 - p 0) / 4 := by rw [← hpx]; simp
  simp [x16] at h2
  apply vec1_ext
  simp [x16]
  nlinarith [hp.1, hp.2]

lemma hA6 : M.A6 hf (1/8) := by
  refine ⟨by norm_num, ?_⟩
  have : M.optimalPrice hf ⟨M.thetaStar, M.thetaStar_mem⟩ = p34 := by
    unfold Model.optimalPrice; rw [xstar]
    apply vec1_ext; simp [M, x16, p34]; norm_num
  rw [this]
  intro p hp
  rw [Metric.mem_closedBall, dist1, abs_le] at hp
  show p ∈ {p : Vec 1 | ∀ j : Fin 1, (WithLp.toLp 2 (fun _ => (0:ℝ)) : Vec 1) j ≤ p j ∧
    p j ≤ (WithLp.toLp 2 (fun _ => (1:ℝ)) : Vec 1) j}
  simp only [Set.mem_ofPred_eq, box_iff]
  simp [p34] at hp
  constructor <;> linarith [hp.1, hp.2]


@[simp] lemma M_demand : M.demand = dem := rfl
@[simp] lemma M_Θ : M.Θ = {0} := rfl

lemma half_mem : (WithLp.toLp 2 (fun _ => (1/2:ℝ)) : Vec 1) ∈ M.prices := by
  show _ ∈ {p : Vec 1 | ∀ j : Fin 1, (WithLp.toLp 2 (fun _ => (0:ℝ)) : Vec 1) j ≤ p j ∧
    p j ≤ (WithLp.toLp 2 (fun _ => (1:ℝ)) : Vec 1) j}
  simp only [Set.mem_ofPred_eq, box_iff]; norm_num

@[reducible] noncomputable def E : ExplorationPrices M where
  count := 1
  count_pos := by norm_num
  price := fun _ => ⟨WithLp.toLp 2 (fun _ => (1/2:ℝ)), half_mem⟩

noncomputable def aY (y : Fin 1 → Sale 1) : ℝ := (y 0).elim (7/8) (fun _ => 1/8)
noncomputable def bY (y : Fin 1 → Sale 1) : ℝ := (y 0).elim (-1/16) (fun _ => 1/16)

lemma BL_eq (z : Vec 1) (y : Fin 1 → Sale 1) :
    E.blockLikelihood z y = aY y + bY y * Real.sin (z 0) := by
  unfold ExplorationPrices.blockLikelihood
  show ∏ s : Fin 1, _ = _
  rw [Fin.prod_univ_one]
  simp only [M_demand]
  cases h : y 0 with
  | none =>
    simp [categoricalMass, aY, bY, h, E]; ring
  | some j =>
    fin_cases j
    simp [categoricalMass, aY, bY, h, E]; ring

lemma aY_pos (y : Fin 1 → Sale 1) (s : ℝ) : 0 < aY y + bY y * Real.sin s := by
  have h1 := Real.neg_one_le_sin s
  have h2 := Real.sin_le_one s
  cases h : y 0 <;> simp [aY, bY, h] <;> nlinarith

lemma aY_pos' (y : Fin 1 → Sale 1) : 0 < aY y := by
  simpa using aY_pos y 0

section logs
variable (a b : ℝ) (hp : ∀ s, 0 < a + b * Real.sin s)
include hp

lemma hasDeriv_log (s : ℝ) :
    HasDerivAt (fun t => Real.log (a + b * Real.sin t)) (b * Real.cos s / (a + b * Real.sin s)) s := by
  have h := ((Real.hasDerivAt_sin s).const_mul b).const_add a
  have := h.log (hp s).ne'
  convert this using 1

lemma cd_log (z : Vec 1) :
    coordDeriv (fun z : Vec 1 => Real.log (a + b * Real.sin (z 0))) z 0 =
      b * Real.cos (z 0) / (a + b * Real.sin (z 0)) := by
  unfold coordDeriv
  simp only [line_apply]
  have h1 : HasDerivAt (fun t : ℝ => z 0 + t) 1 0 := (hasDerivAt_id 0).const_add _
  have h := (hasDeriv_log a b hp (z 0 + 0)).comp 0 h1
  have h' : HasDerivAt (fun t : ℝ => Real.log (a + b * Real.sin (z 0 + t)))
      (b * Real.cos (z 0 + 0) / (a + b * Real.sin (z 0 + 0)) * 1) 0 := h
  rw [h'.deriv]; simp

lemma hasDeriv_q (s : ℝ) :
    HasDerivAt (fun t => b * Real.cos t / (a + b * Real.sin t))
      ((b * -Real.sin s * (a + b * Real.sin s) - b * Real.cos s * (b * Real.cos s)) /
        (a + b * Real.sin s) ^ 2) s := by
  have h1 := (Real.hasDerivAt_cos s).const_mul b
  have h2 := ((Real.hasDerivAt_sin s).const_mul b).const_add a
  exact h1.div h2 (hp s).ne'

lemma sp_log :
    secondPartial (fun z : Vec 1 => Real.log (a + b * Real.sin (z 0))) 0 0 0 = -(b ^ 2 / a ^ 2) := by
  unfold secondPartial
  have : (fun z : Vec 1 => coordDeriv (fun z : Vec 1 => Real.log (a + b * Real.sin (z 0))) z 0)
      = fun z => b * Real.cos (z 0) / (a + b * Real.sin (z 0)) := by
    funext z; exact cd_log a b hp z
  rw [this]; unfold coordDeriv
  simp only [line_apply]
  have h := hasDeriv_q a b hp 0
  have h' : HasDerivAt (fun t : ℝ => b * Real.cos ((0 : Vec 1) 0 + t) / (a + b * Real.sin ((0 : Vec 1) 0 + t)))
      ((b * -Real.sin 0 * (a + b * Real.sin 0) - b * Real.cos 0 * (b * Real.cos 0)) /
        (a + b * Real.sin 0) ^ 2) 0 := by simpa using h
  rw [h'.deriv]; simp; ring

lemma diff1 (z : Vec 1) : DifferentiableAt ℝ
    (fun t : ℝ => Real.log (a + b * Real.sin ((z + t • coordinate 0 : Vec 1) 0))) 0 := by
  simp only [line_apply]
  have h1 : HasDerivAt (fun t : ℝ => z 0 + t) 1 0 := (hasDerivAt_id 0).const_add _
  exact ((hasDeriv_log a b hp (z 0 + 0)).comp 0 h1).differentiableAt

lemma diff2 (z : Vec 1) : DifferentiableAt ℝ
    (fun t : ℝ => coordDeriv (fun z : Vec 1 => Real.log (a + b * Real.sin (z 0)))
      (z + t • coordinate 0) 0) 0 := by
  simp only [cd_log a b hp, line_apply]
  have h1 : HasDerivAt (fun t : ℝ => z 0 + t) 1 0 := (hasDerivAt_id 0).const_add _
  exact ((hasDeriv_q a b hp (z 0 + 0)).comp 0 h1).differentiableAt

end logs


lemma logBL_eq (y : Fin 1 → Sale 1) :
    (fun z : Vec 1 => Real.log (E.blockLikelihood z y)) =
      fun z => Real.log (aY y + bY y * Real.sin (z 0)) := by
  funext z; rw [BL_eq]

lemma term_eq (y : Fin 1 → Sale 1) :
    E.blockLikelihood 0 y * (-secondPartial (fun z => Real.log (E.blockLikelihood z y)) 0 0 0)
      = bY y ^ 2 / aY y := by
  rw [logBL_eq, sp_log _ _ (aY_pos y), BL_eq]
  have := aY_pos' y
  simp; field_simp

lemma fisher_ge : 1/32 ≤ E.fisher 0 0 0 := by
  unfold ExplorationPrices.fisher
  have hnn : ∀ y ∈ (Finset.univ : Finset (Fin E.count → Sale 1)),
      0 ≤ E.blockLikelihood 0 y * (-secondPartial (fun z => Real.log (E.blockLikelihood z y)) 0 0 0) := by
    intro y _
    have := term_eq y
    rw [this]; exact div_nonneg (sq_nonneg _) (aY_pos' y).le
  have h := Finset.single_le_sum hnn (Finset.mem_univ (fun _ => some 0))
  refine le_trans (le_of_eq ?_) h
  have := term_eq (fun _ => some 0)
  have hv : (bY fun _ => some 0) ^ 2 / (aY fun _ => some 0) = 1/32 := by simp [aY, bY]; norm_num
  rw [hv] at this
  exact this.symm

lemma hA5 : E.A5 := by
  refine ⟨?_, 1/16, 1/2, 1/32, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro θ hθ θ' hθ' hne
    exact absurd ((mem0 hθ).trans (mem0 hθ').symm) hne
  · intro θ hθ s
    obtain rfl := mem0 hθ
    refine ⟨fun j => ?_, ?_⟩
    · fin_cases j; simp [E]; norm_num
    · simp [E]; norm_num
  · intro θ hθ y i j
    obtain rfl := mem0 hθ
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    have e : (fun z : Vec 1 => Real.log (E.blockLikelihood z y)) =
        fun z => Real.log (aY y + bY y * Real.sin (z 0)) := logBL_eq y
    have e1 : (fun t : ℝ => Real.log (E.blockLikelihood (0 + t • coordinate 0) y)) =
        fun t => Real.log (aY y + bY y * Real.sin ((0 + t • coordinate 0 : Vec 1) 0)) :=
      funext fun t => congrArg Real.log (BL_eq _ y)
    rw [e, e1]
    exact ⟨diff1 _ _ (aY_pos y) 0, diff2 _ _ (aY_pos y) 0⟩
  · intro θ hθ
    obtain rfl := mem0 hθ
    refine ⟨fun i j => by fin_cases i; fin_cases j; rfl, fun z => ?_⟩
    simp only [Fin.sum_univ_one, norm_sq1]
    have := fisher_ge
    show 1/32 * z 0 ^ 2 ≤ z 0 * E.fisher 0 0 0 * z 0
    nlinarith [sq_nonneg (z 0)]


@[simp] lemma M_A : M.A = fun _ _ => 1 := rfl
@[simp] lemma M_C : M.C = fun _ => 1/8 := rfl
@[simp] lemma M_T : M.T = 2 := rfl
@[simp] lemma M_thetaStar : M.thetaStar = 0 := rfl

lemma load_eq (θ x : Vec 1) : (M.program θ).load x 0 = x 0 := by
  simp [Model.program, CapacityProgram.load]

lemma lag_eq (μ : Fin 1 → ℝ) (x : Vec 1) :
    (M.program 0).lagrangian μ x = x 0 * (1 - 4 * x 0) + μ 0 * (1/16 - x 0) := by
  unfold CapacityProgram.lagrangian
  rw [Fin.sum_univ_one, load_eq]
  have : (M.program 0).objective x = M.revenue 0 x := rfl
  rw [this, rev_eq]
  simp [Model.program]; norm_num

noncomputable def x8 : Vec 1 := WithLp.toLp 2 (fun _ => (1/8 : ℝ))

lemma x8_mem : x8 ∈ (M.program 0).domain := by
  show x8 ∈ M.rates 0
  rw [rates_eq]
  refine ⟨WithLp.toLp 2 (fun _ => (1/2:ℝ)), ?_, ?_⟩
  · simp; norm_num
  · apply vec1_ext; simp [x8]; norm_num

lemma dual0 (μ : Fin 1 → ℝ) (h : μ 0 = 0) : 1/16 ≤ (M.program 0).dualValue μ := by
  unfold CapacityProgram.dualValue
  apply le_csSup
  · refine ⟨1/16, ?_⟩
    rintro _ ⟨x, -, rfl⟩
    rw [lag_eq, h]; nlinarith [sq_nonneg (2 * x 0 - 1/4)]
  · refine ⟨x8, x8_mem, ?_⟩
    rw [lag_eq, h]; simp [x8]; norm_num

lemma dualHalf : (M.program 0).dualValue (fun _ => 1/2) ≤ 3/64 := by
  unfold CapacityProgram.dualValue
  apply csSup_le (Set.Nonempty.image _ ⟨x8, x8_mem⟩)
  rintro _ ⟨x, -, rfl⟩
  rw [lag_eq]; nlinarith [sq_nonneg (2 * x 0 - 1/8)]

lemma revDeriv (θ : M.Θ) : coordDeriv (M.revenue θ) x16 0 = 1/2 := by
  have : M.revenue θ = fun y : Vec 1 => y 0 * (1 - 4 * y 0) := by funext y; exact rev_eq _ y
  rw [this, coordDeriv_rev]; simp [x16]; norm_num

end S228JPP

open JointParametricPricing.PSC

theorem solution : ¬ (∀ {n m q : ℕ} (M : Model n m q) (hf : M.Feasible)
    (E : ExplorationPrices M) (hA5 : E.A5) (φ : ℝ) (hA6 : M.A6 hf φ),
    ∃ κ δbar : ℝ, 0 < κ ∧ 0 < δbar ∧ ∀ θ : M.Θ,
      (θ : Vec q) ∈ Metric.closedBall M.thetaStar δbar →
      M.optimalPrice hf θ ∈ Metric.closedBall (M.optimalPrice hf ⟨M.thetaStar, M.thetaStar_mem⟩) (φ / 2) ∧
      Metric.closedBall (M.optimalPrice hf θ) (φ / 2) ⊆ M.prices ∧
      ‖M.optimalRate hf ⟨M.thetaStar, M.thetaStar_mem⟩ - M.optimalRate hf θ‖ ≤
        κ * ‖M.thetaStar - θ‖ ∧
      ∃ μ : Fin m → ℝ, (M.program M.thetaStar).IsDualOptimum μ ∧
        ∀ i, 0 < μ i → (M.program θ).load (M.optimalRate hf θ) i = M.C i) := by
  intro H
  obtain ⟨κ, δ, -, hδ, H⟩ := H S228JPP.M S228JPP.hf S228JPP.E S228JPP.hA5 (1/8) S228JPP.hA6
  obtain ⟨-, -, -, μ, ⟨hμ0, hopt⟩, hcs⟩ :=
    H ⟨S228JPP.M.thetaStar, S228JPP.M.thetaStar_mem⟩ (Metric.mem_closedBall_self hδ.le)
  rw [S228JPP.M_thetaStar] at hopt
  by_cases hpos : 0 < μ 0
  · have h := hcs 0 hpos
    rw [S228JPP.xstar, S228JPP.load_eq] at h
    norm_num [S228JPP.x16] at h
  · have hz : μ 0 = 0 := le_antisymm (not_lt.mp hpos) (hμ0 0)
    have a := S228JPP.dual0 μ hz
    have b := hopt (fun _ => 1/2) (fun _ => by norm_num)
    have c := S228JPP.dualHalf
    linarith

