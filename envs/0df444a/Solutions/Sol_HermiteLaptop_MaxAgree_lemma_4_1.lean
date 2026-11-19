-- Prove2me | solution 1 for HermiteLaptop.MaxAgree.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-18T15:51:30.997942+00:00
-- url     : https://prove2.me/submissions/075024fd-fa68-4557-9c35-435316df6dfc

import Definitions.Def_HermiteLaptop_MaxAgree_KSpokes
import Theorems.Thm_HermiteLaptop_MaxAgree_eq_8_9
import Definitions.Def_HermiteLaptop_MaxAgree_Mixture

set_option autoImplicit false

/- GaussianSpokes.lean -/
section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace HermiteLaptop.MaxAgree

theorem spokeIndex_measurable {k : ℕ} : Measurable (spokeIndex (k := k)) := by
  classical
  unfold spokeIndex
  generalize List.finRange k = l
  induction l with
  | nil => exact measurable_const
  | cons p l ih =>
    have h : MeasurableSet {x : Fin k → ℝ | ∀ q, x q ≤ x p} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun q => measurableSet_le (measurable_pi_apply q) (measurable_pi_apply p))
    simp only [List.find?_cons]
    convert Measurable.ite h (measurable_const (a := p.val)) ih using 1
    ext x
    by_cases hmax : ∀ q, x q ≤ x p <;> simp [hmax]
    all_goals exact fun _ => Classical.propDecidable _

private abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

private theorem spoke_projection_law {n : ℕ} (u v : Euc n)
    (hu : ⟪u,u⟫ = 1) (hv : ⟪v,v⟫ = 1) :
    (stdGaussian (Euc n)).map (fun g => (⟪u,g⟫, ⟪v,g⟫)) =
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun (z : ℝ × ℝ) =>
      (z.1, ⟪u,v⟫*z.1 + Real.sqrt (1-⟪u,v⟫^2)*z.2)) := by
  let ρ := ⟪u,v⟫
  let s := Real.sqrt (1-ρ^2)
  have hnu : ‖u‖^2 = 1 := (real_inner_self_eq_norm_sq _).symm.trans hu
  have hnv : ‖v‖^2 = 1 := (real_inner_self_eq_norm_sq _).symm.trans hv
  have hra : |ρ| ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    have u1 : ‖u‖ = 1 := by nlinarith [norm_nonneg u]
    have v1 : ‖v‖ = 1 := by nlinarith [norm_nonneg v]
    simpa [ρ, u1, v1] using h
  have hs : s^2 = 1-ρ^2 := Real.sq_sqrt (by nlinarith [abs_le.mp hra, sq_abs ρ])
  apply Measure.ext_of_charFunDual
  funext L
  let a := L (1,0)
  let b := L (0,1)
  have hL (x y : ℝ) : L (x,y) = a*x + b*y := by
    rw [show (x,y) = x • ((1,0):ℝ×ℝ) + y • ((0,1):ℝ×ℝ) by ext <;> simp, map_add, map_smul, map_smul]
    dsimp [a,b]; ring
  have hnorm : ‖a • u + b • v‖^2 = (a+b*ρ)^2 + (b*s)^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hu,hv, real_inner_comm u v]
    change _ = (a+b*⟪u,v⟫)^2+(b*s)^2
    rw [mul_pow, hs]
    dsimp [ρ]; ring
  simp only [charFunDual_apply]
  rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  calc
    _ = charFun (stdGaussian (Euc n)) (a • u + b • v) := by
      rw [charFun_apply]
      apply integral_congr_ae
      filter_upwards with g
      rw [hL, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm g u, real_inner_comm g v]
    _ = charFun (gaussianReal 0 1) (a+b*ρ) * charFun (gaussianReal 0 1) (b*s) := by
      rw [charFun_stdGaussian, charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add]
      push_cast
      congr 1
      have hn := congrArg (fun x : ℝ => (x:ℂ)) hnorm
      push_cast at hn
      linear_combination -hn / 2
    _ = _ := by
      rw [charFun_apply_real, charFun_apply_real, ← integral_prod_mul]
      apply integral_congr_ae
      filter_upwards with z
      rw [← Complex.exp_add, hL]
      congr 1
      push_cast
      dsimp [ρ,s]; ring

/-- The collision event for two vertices has the scalar collision probability. -/
theorem spoke_same_mean {n : ℕ} (k : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, ⟪v i,v i⟫ = 1) (e : Sym2 (Fin n)) :
    (∫ g, sameInd (kSpokes v g) e ∂spokeMeasure n k) = collisionProb k (edgeInner v e) := by
  induction e using Sym2.inductionOn with
  | _ i j =>
    let ρ := ⟪v i,v j⟫
    let γ := gaussianReal 0 1
    let F := fun g : Euc n => (⟪v i,g⟫,⟪v j,g⟫)
    let G := fun z : ℝ × ℝ => (z.1,ρ*z.1+Real.sqrt (1-ρ^2)*z.2)
    let Z := (γ.prod γ).map G
    have H1 : MeasurePreserving F (stdGaussian (Euc n)) Z :=
      ⟨by dsimp [F]; fun_prop, spoke_projection_law (v i) (v j) (hv i) (hv j)⟩
    have H2 : MeasurePreserving G (γ.prod γ) Z := ⟨by dsimp [G]; fun_prop,rfl⟩
    let pack := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)
    have HP : MeasurePreserving pack (Measure.pi fun _ => γ.prod γ) ((gaussPi k).prod (gaussPi k)) :=
      measurePreserving_arrowProdEquivProdArrow _ _ _ (fun _ => γ) (fun _ => γ)
    have HF := measurePreserving_pi (fun _ : Fin k => stdGaussian (Euc n)) (fun _ => Z) (fun _ => H1)
    have HG := (measurePreserving_pi (fun _ : Fin k => γ.prod γ) (fun _ => Z) (fun _ => H2)).comp
      (MeasurePreserving.symm pack HP)
    let S : Set (Fin k → ℝ × ℝ) := {z | spokeIndex (fun q => (z q).1) = spokeIndex (fun q => (z q).2)}
    have hm : MeasurableSet S := measurableSet_eq_fun (spokeIndex_measurable.comp (by fun_prop))
      (spokeIndex_measurable.comp (by fun_prop))
    have hF := HF.measure_preimage hm.nullMeasurableSet
    have hG := HG.measure_preimage hm.nullMeasurableSet
    let T : Set (Fin k → Euc n) := (fun g q => F (g q)) ⁻¹' S
    have hT : MeasurableSet T := HF.measurable hm
    have he : (fun g => sameInd (kSpokes v g) s(i,j)) =
        T.indicator (fun _ => (1:ℝ)) := by
      funext g
      change (if kSpokes v g i = kSpokes v g j then (1:ℝ) else 0) = _
      by_cases h : kSpokes v g i = kSpokes v g j
      · rw [if_pos h, Set.indicator_of_mem (show g ∈ T from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show g ∉ T from h)]
    rw [he, integral_indicator hT]
    simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    change ((Measure.pi fun _ : Fin k => stdGaussian (Euc n)) T).toReal = _
    exact congrArg ENNReal.toReal (hF.trans hG.symm)

end HermiteLaptop.MaxAgree
end

/- Ratio.lean -/
section
open MeasureTheory ProbabilityTheory
namespace HermiteLaptop.MaxAgree
open Finset Set
private abbrev D := Set.Ico (-1/2 : ℝ) 1

private theorem oddPowerMono (n : ℕ) : MonotoneOn (fun x : ℝ => x^(2*n+1)) D := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico ..) (by fun_prop) (by fun_prop)
  intro x hx
  rw [(hasDerivAt_pow (2*n+1) x).deriv]
  simp only [Nat.add_sub_cancel]
  exact mul_nonneg (Nat.cast_nonneg _) (by rw [pow_mul]; positivity)

private theorem pairPowerMono (n : ℕ) :
    MonotoneOn (fun x : ℝ => x^(2*n+1) + x^(2*n+2)) D := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico ..) (by fun_prop) (by fun_prop)
  intro x hx
  have hx' : -1/2 ≤ x := (interior_subset hx).1
  change 0 ≤ deriv ((fun x : ℝ => x^(2*n+1)) + (fun x : ℝ => x^(2*n+2))) x
  rw [((hasDerivAt_pow (2*n+1) x).add (hasDerivAt_pow (2*n+2) x)).deriv]
  simp only [Nat.add_sub_cancel, show 2*n+2-1 = 2*n+1 by omega, pow_succ x (2*n), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hp : 0 ≤ x^(2*n) := by rw [pow_mul]; positivity
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hh : 0 ≤ (2*(n:ℝ)+1) + (2*(n:ℝ)+2)*x := by
    nlinarith [mul_nonneg (show 0 ≤ 2*(n:ℝ)+2 by positivity) (show 0 ≤ x + 1/2 by linarith)]
  nlinarith only [mul_nonneg hp hh]

private def Q (m : ℕ) (x : ℝ) := ∑ i ∈ range m, x^i
private theorem qOdd (n : ℕ) : MonotoneOn (Q (2*n+1)) D := by
  induction n with
  | zero => intro x hx y hy h; simp [Q]
  | succ n ih =>
    intro x hx y hy h
    have hh := pairPowerMono n hx hy h
    have hp := ih hx hy h
    change _ + _ ≤ _ + _ at hh
    change (∑ i ∈ range (2*n+1), x^i) ≤ ∑ i ∈ range (2*n+1), y^i at hp
    simp only [Q, show 2*(n+1)+1 = (2*n+1)+1+1 by omega, sum_range_succ _ (2*n+1+1),
      sum_range_succ _ (2*n+1), show 2*n+1+1 = 2*n+2 by omega]
    linarith

private theorem geoMono (m : ℕ) : MonotoneOn (Q m) D := by
  by_cases h : m=0
  · subst m
    simp [Q, MonotoneOn]
  by_cases ho : m%2 = 1
  · rw [show m=2*(m/2)+1 by omega]
    exact qOdd _
  obtain ⟨n, hn⟩ : ∃ n, m=2*n+1+1 := ⟨(m-2)/2, by omega⟩
  rw [hn]
  intro x hx y hy h
  simpa only [Q, sum_range_succ] using add_le_add (qOdd n hx hy h) (oddPowerMono n hx hy h)

private theorem ratio_collision_one (k : ℕ) : collisionProb k 1 = 1 := by
  have h (x y : Fin k → ℝ) : corrPartner 1 x y = x := by
    ext i
    simp [corrPartner]
  simp [collisionProb, h, gaussPi]

/-- Monotonicity of the normalized separation probability follows by pairing
successive powers in each finite geometric sum. -/
theorem ratio_mono_of_series (k : ℕ) (hk : 1 ≤ k) :
    MonotoneOn (fun x : ℝ => (1-collisionProb k x)/(1-x)) (Ico (-1/2 : ℝ) 1) := by
  have ha : HasSum (coeffC k) 1 := by
    simpa [ratio_collision_one] using ((eq_8_9 k hk).1 1 (by constructor <;> norm_num)).2.2
  have hr (x : ℝ) (hx : x ∈ D) :
      HasSum (fun m => coeffC k m * Q m x) ((1-collisionProb k x)/(1-x)) := by
    have hD : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
    have h := (ha.sub ((eq_8_9 k hk).1 x hD).2.2).div_const (1-x)
    apply h.congr_fun
    intro m
    symm
    change (coeffC k m - coeffC k m * x ^ m)/(1-x) = _
    rw [div_eq_iff (sub_ne_zero.mpr hx.2.ne')]
    rw [mul_assoc, Q, geom_sum_mul_neg]
    ring
  intro x hx y hy hxy
  exact hasSum_le (fun m => mul_le_mul_of_nonneg_left (geoMono m hx hy hxy) ((eq_8_9 k hk).2 m).2)
    (hr x hx) (hr y hy)

/-- The same monotonicity for every countable mixture of positive spoke counts. -/
theorem mixture_ratio_mono_of_series (μ : Mixture) :
    MonotoneOn (fun x : ℝ => (1-μ.collision x)/(1-x)) (Ico (-1/2 : ℝ) 1) := by
  have hsum (x : ℝ) :
      HasSum (fun k => μ.lam k * ((1-collisionProb k x)/(1-x))) ((1-μ.collision x)/(1-x)) := by
    have hw (k : ℕ) : 0 ≤ collisionProb k x := ENNReal.toReal_nonneg
    have hb (k : ℕ) : collisionProb k x ≤ 1 := by
      unfold collisionProb gaussPi
      exact MeasureTheory.measureReal_le_one
    have hs : Summable (fun k => μ.lam k * collisionProb k x) := Summable.of_nonneg_of_le
      (fun k => mul_nonneg (μ.lam_nonneg k) (hw k))
      (fun k => mul_le_of_le_one_right (μ.lam_nonneg k) (hb k)) μ.lam_sum.summable
    apply ((μ.lam_sum.sub hs.hasSum).div_const (1-x)).congr_fun
    intro i
    symm
    change (μ.lam i-μ.lam i*collisionProb i x)/(1-x) = _
    ring
  intro x hx y hy hxy
  apply hasSum_le _ (hsum x) (hsum y)
  intro k
  by_cases hk : k ∈ μ.K
  · exact mul_le_mul_of_nonneg_left (ratio_mono_of_series k (μ.K_pos k hk) hx hy hxy) (μ.lam_nonneg k)
  · simp [μ.lam_zero_off k hk]

end HermiteLaptop.MaxAgree
end

/- Sol_HermiteLaptop_MaxAgree_lemma_4_1.lean -/
section
open MeasureTheory ProbabilityTheory HermiteLaptop.MaxAgree Finset
open scoped RealInnerProductSpace

private theorem kSpokes_measurable {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    Measurable (fun g : Fin k → EuclideanSpace ℝ (Fin n) => kSpokes v g i) := by
  apply spokeIndex_measurable.comp
  apply measurable_pi_lambda
  intro q
  exact (continuous_const.inner (continuous_apply q)).measurable

private theorem sameIndicator_integrable {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) (e : Sym2 (Fin n)) : Integrable (fun g : Fin k → EuclideanSpace ℝ (Fin n) =>
      sameInd (kSpokes v g) e) (spokeMeasure n k) := by
    let : IsProbabilityMeasure (spokeMeasure n k) := by unfold spokeMeasure; infer_instance
    induction e using Sym2.inductionOn with
    | _ i j =>
      have hm := measurableSet_eq_fun (kSpokes_measurable (k := k) v i) (kSpokes_measurable v j)
      have heq : (fun g : Fin k → EuclideanSpace ℝ (Fin n) => sameInd (kSpokes v g) s(i, j)) =
          ({g | kSpokes v g i = kSpokes v g j} : Set (Fin k → EuclideanSpace ℝ (Fin n))).indicator (fun _ => (1 : ℝ)) := by
        funext g
        by_cases hsame : kSpokes v g i = kSpokes v g j <;> simp [sameInd, hsame]
      rw [heq]
      exact (integrable_const (μ := spokeMeasure n k) (1 : ℝ)).indicator hm

private theorem single_spoke_objective {n k : ℕ} (I : Instance n) (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hpair : ∀ e, (∫ g, sameInd (kSpokes v g) e ∂spokeMeasure n k) = collisionProb k (edgeInner v e)) :
    I.spokesValue k v = (∑ e ∈ I.Epos, I.w e * collisionProb k (edgeInner v e)) +
      ∑ e ∈ I.Eneg, I.w e * (1-collisionProb k (edgeInner v e)) := by
  let : IsProbabilityMeasure (spokeMeasure n k) := by unfold spokeMeasure; infer_instance
  let f := fun e (g : Fin k → EuclideanSpace ℝ (Fin n)) => sameInd (kSpokes v g) e
  have hi (e) : Integrable (f e) (spokeMeasure n k) := sameIndicator_integrable v e
  have hp (e) := (hi e).const_mul (I.w e)
  have hn (e) := ((integrable_const (μ := spokeMeasure n k) (1:ℝ)).sub (hi e)).const_mul (I.w e)
  unfold Instance.spokesValue Instance.val
  refine (integral_add (integrable_finsetSum I.Epos fun e _ => hp e) (integrable_finsetSum I.Eneg fun e _ => hn e)).trans ?_
  rw [integral_finsetSum I.Epos (fun e _ => hp e), integral_finsetSum I.Eneg (fun e _ => hn e)]
  simp only [Pi.sub_apply, integral_const_mul, f, hpair,
    integral_sub (integrable_const (1:ℝ)) (sameIndicator_integrable v _), integral_const,
    probReal_univ, one_smul]

private theorem mixture_collision_hasSum (μ : Mixture) (ρ : ℝ) :
    HasSum (fun k => μ.lam k * collisionProb k ρ) (μ.collision ρ) := by
  apply Summable.hasSum
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (μ.lam_nonneg k) ENNReal.toReal_nonneg) _ μ.lam_sum.summable
  intro k
  apply mul_le_of_le_one_right (μ.lam_nonneg k)
  let : IsProbabilityMeasure (gaussPi k) := by unfold gaussPi; infer_instance
  exact measureReal_le_one

private theorem mixture_objective {n : ℕ} (I : Instance n) (v : Fin n → EuclideanSpace ℝ (Fin n))
    (μ : Mixture) (hpair : ∀ k e, (∫ g, sameInd (kSpokes v g) e ∂spokeMeasure n k) =
       collisionProb k (edgeInner v e)) :
    μ.value I v = (∑ e ∈ I.Epos, I.w e * μ.collision (edgeInner v e)) +
        ∑ e ∈ I.Eneg, I.w e * (1-μ.collision (edgeInner v e)) := by
  have h (e) := mixture_collision_hasSum μ (edgeInner v e)
  have hp := hasSum_sum (s := I.Epos) fun e _ => (h e).mul_left (I.w e)
  have hn := hasSum_sum (s := I.Eneg) fun e _ => (μ.lam_sum.sub (h e)).mul_left (I.w e)
  apply HasSum.tsum_eq (f := fun k => μ.lam k * I.spokesValue k v)
  refine (hp.add hn).congr_fun (fun k => ?_)
  rw [single_spoke_objective I v (hpair k), mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply sum_congr rfl
    intro e _
    ring
  · apply sum_congr rfl
    intro e _
    ring

private theorem edge_inner_mem {n : ℕ} {a : ℝ} {v : Fin n → EuclideanSpace ℝ (Fin n)}
    (hv : SDPFeasible a v) (e : Sym2 (Fin n)) : edgeInner v e ∈ Set.Icc a 1 := by
  induction e using Sym2.inductionOn with
  | _ i j =>
    have hn (i : Fin n) : ‖v i‖ = 1 := by
      have hh := hv.1 i
      rw [real_inner_self_eq_norm_sq] at hh
      nlinarith [norm_nonneg (v i)]
    refine ⟨hv.2 i j, ?_⟩
    change ⟪v i, v j⟫ ≤ 1
    simpa [hn] using real_inner_le_norm (v i) (v j)

private theorem negative_edge_bound (μ : Mixture) {γ a ρ : ℝ}
    (ha : a ∈ Set.Icc (-1/2 : ℝ) 0) (hρ : ρ ∈ Set.Icc a 1) (hneg : γ ≤ 1-μ.collision a) :
    γ * sMinus a ρ ≤ 1-μ.collision ρ := by
  have hca := (mixture_collision_hasSum μ ρ)
  by_cases he : ρ=1
  · subst ρ
    have hm := hasSum_le (g := μ.lam) (fun k => by
      apply mul_le_of_le_one_right (μ.lam_nonneg k)
      let : IsProbabilityMeasure (gaussPi k) := by unfold gaussPi; infer_instance
      exact measureReal_le_one) hca μ.lam_sum
    simp [sMinus]
    linarith
  have hρ' : ρ < 1 := lt_of_le_of_ne hρ.2 he
  have ha' : a < 1 := lt_of_le_of_lt ha.2 zero_lt_one
  have hr := mixture_ratio_mono_of_series μ (show a ∈ Set.Ico (-1/2:ℝ) 1 from ⟨ha.1,ha'⟩)
    (show ρ ∈ Set.Ico (-1/2:ℝ) 1 from ⟨ha.1.trans hρ.1, hρ'⟩) hρ.1
  change (1 - μ.collision a)/(1-a) ≤ (1-μ.collision ρ)/(1-ρ) at hr
  have ht := ((div_le_div_iff₀ (sub_pos.mpr ha') (sub_pos.mpr hρ')).mp hr)
  rw [sMinus, ← mul_div_assoc, div_le_iff₀ (sub_pos.mpr ha')]
  exact (mul_le_mul_of_nonneg_right hneg (sub_nonneg.mpr hρ.2)).trans ht

private theorem edgewise_from_pairs {n : ℕ} (I : Instance n) (F : Set (Fin n → ℕ)) (a : ℝ)
    (ha : a ∈ Set.Icc (-1/2 : ℝ) 0) (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : I.SDPOptimal a v) (hrelax : ∀ C ∈ F, I.val C ≤ I.sdpObj a v) (μ : Mixture)
    (γ : ℝ) (hγ : 0 ≤ γ) (hpos : ∀ ρ ∈ Set.Icc a 1, γ*sPlus a ρ ≤ μ.collision ρ)
    (hneg : γ ≤ 1-μ.collision a)
    (hpair : ∀ k e, (∫ g, sameInd (kSpokes v g) e ∂spokeMeasure n k) = collisionProb k (edgeInner v e)) :
    ∀ C ∈ F, γ * I.val C ≤ μ.value I v := by
  intro C hC
  apply (mul_le_mul_of_nonneg_left (hrelax C hC) hγ).trans
  rw [mixture_objective I v μ hpair, Instance.sdpObj, mul_add, Finset.mul_sum, Finset.mul_sum]
  apply add_le_add <;> apply sum_le_sum <;> intro e he <;> rw [mul_left_comm]
  · exact mul_le_mul_of_nonneg_left (hpos _ (edge_inner_mem hv.1 e)) (I.w_pos_pos e he).le
  · exact mul_le_mul_of_nonneg_left (negative_edge_bound μ ha (edge_inner_mem hv.1 e) hneg) (I.w_pos_neg e he).le

theorem solution {n : ℕ} (I : Instance n) (F : Set (Fin n → ℕ)) (a : ℝ)
    (ha : a ∈ Set.Icc (-1 / 2 : ℝ) 0) (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : I.SDPOptimal a v) (hrelax : ∀ C ∈ F, I.val C ≤ I.sdpObj a v) (μ : Mixture)
    (hfeas : ∀ k : ℕ, μ.lam k ≠ 0 → ∀ g : Fin k → EuclideanSpace ℝ (Fin n), kSpokes v g ∈ F)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hpos : ∀ ρ ∈ Set.Icc a 1, γ * sPlus a ρ ≤ μ.collision ρ)
    (hneg : γ ≤ 1 - μ.collision a) :
    ∀ C ∈ F, γ * I.val C ≤ μ.value I v := by
  exact edgewise_from_pairs I F a ha v hv hrelax μ γ hγ hpos hneg
    (fun k e => spoke_same_mean k v hv.1.1 e)
end
