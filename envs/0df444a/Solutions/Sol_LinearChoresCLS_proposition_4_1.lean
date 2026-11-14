-- Prove2me | solution 1 for LinearChoresCLS.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:40:17.820205+00:00
-- url     : https://prove2.me/submissions/4ed921bf-038c-4147-bcb6-87958bd292af

import Definitions.Def_LinearChoresCLS_EpsKKT
import Definitions.Def_LinearChoresCLS_RightDeriv
import Definitions.Def_LinearChoresCLS_Psi

open Finset LinearChoresCLS
section
variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
variable {F : ChoresMarket N M} {p : M → ℝ} {z : N → M → ℝ}

private theorem ratio_le_mu (a : N) (j : M) : p j / F.disutil a j ≤ F.mu a p :=
  Finset.le_sup' (fun k => p k / F.disutil a k) (Finset.mem_univ j)

/-- A one-chore optimal-ratio bundle witnesses the minimum disutility.
Equality in the resulting weighted sum forces every used chore to attain the ratio. -/
private theorem demand_conditions (hF : F.Valid) (hCE : F.IsCE p z) (a : N) :
    (∑ j, p j * z a j) = F.earn a ∧
    0 < F.mu a p ∧ ∀ j, 0 < z a j → p j / F.disutil a j = F.mu a p := by
  classical
  obtain ⟨hz, hbudget, hopt⟩ := hCE.2.2.1 a
  have hpospay : 0 < ∑ j, p j * z a j := lt_of_lt_of_le (hF.2.1 a) hbudget
  obtain ⟨i, hi⟩ : ∃ i, 0 < p i * z a i := by
    by_contra! hall
    exact hpospay.not_ge (Finset.sum_nonpos (fun i _ => hall i))
  have hpi : 0 < p i := by
    by_contra! h
    rw [le_antisymm h (hCE.1 i), zero_mul] at hi
    exact hi.false
  have hmu : 0 < F.mu a p :=
    lt_of_lt_of_le (div_pos hpi (hF.1 a i)) (ratio_le_mu a i)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' (univ_nonempty : (univ : Finset M).Nonempty)
    (fun j => p j / F.disutil a j)
  change F.mu a p = _ at hb
  have hbmul : F.mu a p * F.disutil a b = p b := (eq_div_iff (hF.1 a b).ne').mp hb
  have hpb : 0 < p b := by rw [← hbmul]; exact mul_pos hmu (hF.1 a b)
  let y : M → ℝ := fun j => if j = b then F.earn a / p b else 0
  have hy : ∀ j, 0 ≤ y j := by
    intro j
    dsimp [y]
    split_ifs
    · exact div_nonneg (hF.2.1 a).le hpb.le
    · exact le_rfl
  have hyval : ∑ j, p j * y j = F.earn a := by
    simp [y, mul_ite]
    field_simp
  have hycost : ∑ j, F.disutil a j * y j = F.disutil a b * (F.earn a / p b) := by
    simp [y, mul_ite]
  have hcost := hopt y hy hyval.ge
  rw [hycost] at hcost
  have hcap : F.mu a p * (∑ j, F.disutil a j * z a j) ≤ F.earn a := calc
    _ ≤ F.mu a p * (F.disutil a b * (F.earn a / p b)) := mul_le_mul_of_nonneg_left hcost hmu.le
    _ = _ := by rw [← mul_assoc, hbmul]; field_simp
  have hterm (j : M) : p j * z a j ≤ F.mu a p * (F.disutil a j * z a j) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (hF.1 a j)).mp (ratio_le_mu a j)) (hz j)
  have hsum := Finset.sum_le_sum (s := (univ : Finset M)) (fun j _ => hterm j)
  rw [← Finset.mul_sum] at hsum
  have hearn := le_antisymm (hsum.trans hcap) hbudget
  refine ⟨hearn, hmu, ?_⟩
  intro j hj
  have hgap : ∑ k, (F.mu a p * (F.disutil a k * z a k) - p k * z a k) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  have hg := Finset.single_le_sum (s := (univ : Finset M))
    (f := fun k => F.mu a p * (F.disutil a k * z a k) - p k * z a k)
    (fun k _ => sub_nonneg.mpr (hterm k)) (Finset.mem_univ j)
  rw [hgap] at hg
  apply (div_eq_iff (hF.1 a j).ne').mpr
  apply mul_right_cancel₀ hj.ne'
  rw [mul_assoc]
  exact le_antisymm (hterm j) (sub_nonpos.mp hg)

end
open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash Filter Set Topology

private theorem fromRight {f : ℝ → ℝ} {d : ℝ} :
    HasRightDerivAt0 f d ↔ HasDerivWithinAt f d (Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have he : slope f 0 = (fun h : ℝ => h⁻¹ • (f h-f 0)) := by funext h; simp [slope_def_module]
  rw [he]; rfl

/-- Evaluate the bundle used at equilibrium at the varying prices. Its revenue,
divided by its disutility, supports the maximum price-to-disutility ratio from below. -/
private theorem support {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
    (F : ChoresMarket N M) (hv : F.Valid) (p : M → ℝ) (z : N → M → ℝ) (hCE : F.IsCE p z)
    (γ : ℝ → M → ℝ) (D : M → ℝ) (h0 : γ 0 = p) (hD : HasRightDerivAt0 γ D)
    (hdom : ∀ᶠ h in 𝓝[>] 0, γ h ∈ F.priceDomain) (hp : p ∈ F.priceDomain) :
    ∃ U : ℝ → ℝ, HasRightDerivAt0 U 0 ∧ U 0 = F.Psi p ∧
      ∀ᶠ h in 𝓝[>] 0, F.Psi (γ h) ≤ U h := by
  classical
  let B := F.earn
  let μ := fun a => F.mu a p
  let rev := fun a h => ∑ j, γ h j * z a j
  let δ := fun a => ∑ j, D j * z a j
  have hd (j : M) : HasDerivWithinAt (fun h => γ h j) (D j) (Ioi 0) 0 :=
    fromRight.mp (tendsto_pi_nhds.mp hD j)
  have hrev (a : N) : HasDerivWithinAt (rev a) (δ a) (Ioi 0) 0 :=
    HasDerivWithinAt.fun_sum (fun j _ => (hd j).mul_const _)
  have hB (a : N) : 0 < B a := hv.2.1 a
  have hμ (a : N) : 0 < μ a := (demand_conditions hv hCE a).2.1
  have hr0 (a : N) : rev a 0 = B a := by
    dsimp [rev]; rw [h0]; exact (demand_conditions hv hCE a).1
  have cost (a : N) : μ a * (∑ j, F.disutil a j * z a j) = B a := by
    rw [← hr0, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    change _ = γ 0 j * _
    rw [h0, ← mul_assoc]
    rcases (hCE.2.1 a j).eq_or_lt with he|hz
    · simp [← he]
    · have he := ((div_eq_iff (hv.1 a j).ne').mp ((demand_conditions hv hCE a).2.2 j hz))
      change _ * _ * _ = _; rw [← he]
  have drev : ∑ a, δ a = 0 := by
    have hdPay : HasDerivWithinAt (fun h => ∑ j, F.supply j * γ h j)
        (∑ j, F.supply j * D j) (Ioi 0) 0 :=
      HasDerivWithinAt.fun_sum (fun j _ => (hd j).const_mul _)
    have hc : HasDerivWithinAt (fun _ : ℝ => ∑ a, F.earn a) (∑ j, F.supply j * D j) (Ioi 0) 0 :=
      hdPay.congr_of_eventuallyEq (hdom.mono (fun _ h => h.2.symm)) (by rw [h0]; exact hp.2.symm)
    have hz := tendsto_nhds_unique (fromRight.mpr hc) (show HasRightDerivAt0 (fun _ : ℝ => ∑ a, F.earn a) 0 from
      fromRight.mpr (hasDerivWithinAt_const _ _ _))
    dsimp [δ]; rw [Finset.sum_comm]
    convert hz using 1
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.mul_sum,hCE.2.2.2 j,mul_comm]
  let U := fun h => -∑ a, B a * (Real.log (μ a) + Real.log (rev a h) - Real.log (B a))
  have term (a : N) : HasDerivWithinAt
      (fun h => B a * (Real.log (μ a) + Real.log (rev a h) - Real.log (B a))) (δ a) (Ioi 0) 0 := by
    have hh := (((hrev a).log (by rw [hr0]; exact (hB a).ne')).const_add
      (Real.log (μ a))).sub_const (Real.log (B a))
    have eq : B a * (δ a / rev a 0) = δ a := by rw [hr0]; field_simp [(hB a).ne']
    rw [← eq]; exact hh.const_mul (B a)
  have hU := (HasDerivWithinAt.fun_sum (u := univ) (fun a _ => term a)).neg
  refine ⟨U, fromRight.mpr (by rw [drev,neg_zero] at hU; exact hU), ?_, ?_⟩
  · simp [U,hr0,B,μ,ChoresMarket.Psi]
  have near (a : N) : ∀ᶠ h in 𝓝[>] 0, 0 < rev a h :=
    tendsto_const_nhds.eventually_lt (hrev a).continuousWithinAt.tendsto (by rw [hr0]; exact hB a)
  filter_upwards [Filter.eventually_all.mpr near] with h hh
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hB a).le
  have termle (j : M) : γ h j * z a j ≤ F.mu a (γ h) * (F.disutil a j * z a j) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (hv.1 a j)).mp (ratio_le_mu _ _)) (hCE.2.1 a j)
  have hle := Finset.sum_le_sum (s := univ) (fun j _ => termle j)
  rw [← Finset.mul_sum] at hle
  have hb' : μ a * rev a h ≤ F.mu a (γ h) * B a := calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (hμ a).le
    _ = _ := by rw [mul_left_comm, cost]
  have hl := Real.log_le_log (div_pos (mul_pos (hμ a) (hh a)) (hB a)) ((div_le_iff₀ (hB a)).mpr hb')
  rwa [Real.log_div (mul_pos (hμ a) (hh a)).ne' (hB a).ne',Real.log_mul (hμ a).ne' (hh a).ne'] at hl
private theorem qline {n : ℕ} (P : Quadratic n) (x : Fin n → ℝ) (i : Fin n) (s : Bool) :
    HasDerivAt (fun h : ℝ => quadraticValue P (x + h • coordDir i s))
      ((if s then 1 else -1 : ℝ) * sourceGradient P x i) 0 := by
  classical
  let v := coordDir i s
  have coord (j : Fin n) : HasDerivAt (fun h : ℝ => x j + h * v j) (v j) 0 := by
    simpa only [one_mul,id_eq] using! (((hasDerivAt_id (0:ℝ)).mul_const (v j)).const_add (x j))
  have product (j k : Fin n) : HasDerivAt
      (fun h : ℝ => (P.Q j k : ℝ) * (x j + h*v j) * (x k + h*v k))
      ((P.Q j k : ℝ)*v j*x k + (P.Q j k : ℝ)*x j*v k) 0 := by
    simpa only [zero_mul,add_zero] using! (((coord j).const_mul (P.Q j k : ℝ)).mul (coord k))
  have dq := ((HasDerivAt.fun_sum (u := univ) (fun j _ =>
    HasDerivAt.fun_sum (u := univ) (fun k _ => product j k))).div_const (2:ℝ)).add
    (HasDerivAt.fun_sum (u := univ) (fun j _ => (coord j).const_mul (P.c j : ℝ)))
  let sign : ℝ := if s then 1 else -1
  have hv (j : Fin n) : v j = if j = i then sign else 0 := by simp [v,coordDir,Pi.single_apply,sign,eq_comm]
  have hs (j k : Fin n) : (P.Q j k : ℝ) = (P.Q k j : ℝ) := by rw [P.symmetric]
  have sum₁ : (∑ j, ∑ k, (P.Q j k : ℝ)*v j*x k) = sign * ∑ k, (P.Q i k : ℝ)*x k := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    simp [hv,mul_ite,ite_mul,mul_assoc,mul_left_comm]
  have sum₂ : (∑ j, ∑ k, (P.Q j k : ℝ)*x j*v k) = sign * ∑ j, (P.Q i j : ℝ)*x j := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    simp [hv,mul_ite,hs j i,mul_comm]
  have linear : (∑ j, (P.c j : ℝ)*v j) = (P.c i : ℝ)*sign := by simp [hv,mul_ite]
  have heq : (∑ j, ∑ k, ((P.Q j k : ℝ)*v j*x k + (P.Q j k : ℝ)*x j*v k))/2 +
      (∑ j, (P.c j : ℝ)*v j) = sign * sourceGradient P x i := by
    simp only [Finset.sum_add_distrib,sum₁,sum₂,linear,sourceGradient]
    ring
  rw [heq] at dq
  exact dq

private theorem direction {n : ℕ} {x : Fin n → ℝ} (hx : InCube x) (i : Fin n) (s : Bool)
    (h : if s then x i < 1 else 0 < x i) : FeasibleCoordDir x i s := by
  cases s
  · change 0 < x i at h
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds] with u hu hu'
    intro j
    by_cases e : i=j
    · subst j; simp [coordDir,Pi.single_apply]; constructor <;> linarith [(hx i).2,show 0<u from hu]
    · simpa [coordDir,Pi.single_apply,e,Ne.symm e] using hx j
  · change x i < 1 at h
    have small : 0 < 1-x i := by linarith
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds small).filter_mono nhdsWithin_le_nhds] with u hu hu'
    intro j
    by_cases e : i=j
    · subst j; simp [coordDir,Pi.single_apply]; constructor <;> linarith [(hx i).1,show 0<u from hu]
    · simpa [coordDir,Pi.single_apply,e,Ne.symm e] using hx j

theorem solution {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
    (F : ChoresMarket N M) (hF : F.Valid) {n : ℕ} (P : Quadratic n) (ε : ℝ) (hε : 0<ε)
    (pm : (Fin n → ℝ) → (M → ℝ)) (hdom : ∀ x, InCube x → pm x ∈ F.priceDomain)
    (hderiv : ∀ x, InCube x → ∀ (i : Fin n) (s : Bool), FeasibleCoordDir x i s →
      ∃ D : M → ℝ, HasRightDerivAt0 (fun h => pm (x + h • coordDir i s)) D)
    (herr : ∃ (α C β : ℝ) (R : (Fin n → ℝ) → ℝ), 0 < α ∧
      (∀ x, InCube x → F.Psi (pm x) = C + α * quadraticValue P x + R x) ∧
      0 ≤ β ∧ β ≤ α * ε ∧
      ∀ (x : Fin n → ℝ) (i : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single i (1 : ℝ)) →
        |R (x + h • Pi.single i (1 : ℝ)) - R x| ≤ β * |h|) :
    ∀ x, InCube x → (∃ z : N → M → ℝ, F.IsCE (pm x) z) → IsEpsKKT P ε x := by
  rintro x hx ⟨z,hCE⟩
  obtain ⟨α,C,β,R,hα,hobj,_,hβ,herr⟩ := herr
  have bound (i : Fin n) (s : Bool) (hs : if s then x i < 1 else 0 < x i) :
      (if s then 1 else -1 : ℝ) * sourceGradient P x i ≤ ε := by
    let v := coordDir i s
    have hfeas := direction hx i s hs
    obtain ⟨D,hD⟩ := hderiv x hx i s hfeas
    obtain ⟨U,hU,hU0,hUle⟩ := support F hF (pm x) z hCE (fun h => pm (x+h • v)) D
      (by simp) hD (hfeas.mono (fun h h' => hdom _ h')) (hdom x hx)
    have hq := fromRight.mpr ((qline P x i s).const_mul α).hasDerivWithinAt
    have lim := le_of_tendsto_of_tendsto hq (hU.add (tendsto_const_nhds (x := β))) (by
      filter_upwards [self_mem_nhdsWithin, hfeas, hUle] with u hu hbox hupper
      have hu' : 0 < u := hu
      have err : |R (x + u • v) - R x| ≤ β*u := by
        cases s
        · have hv : u • coordDir i false = (-u) • Pi.single i (1:ℝ) := by
            ext j; simp [coordDir,Pi.single_apply]
          rw [show v = coordDir i false from rfl, hv]
          exact (herr x i (-u) hx (hv ▸ hbox)).trans_eq (by rw [abs_neg,abs_of_pos hu'])
        · simpa [v,coordDir,abs_of_pos hu'] using herr x i u hx hbox
      change _ ≤ U u at hupper
      rw [hobj _ hbox] at hupper
      have hzero := hU0.trans (hobj x hx)
      have low := (abs_le.mp err).1
      change u⁻¹ * (α * quadraticValue P (x+u • v) - α * quadraticValue P (x+0 • v)) ≤
        u⁻¹*(U u-U 0) + β
      rw [zero_smul,add_zero,← div_eq_inv_mul, ← div_eq_inv_mul]
      apply (div_le_iff₀ hu').mpr
      rw [add_mul, div_mul_cancel₀ _ hu'.ne']
      linarith)
    change α * _ ≤ 0 + β at lim
    exact (mul_le_mul_iff_right₀ hα).mp (le_trans (by simpa using lim) hβ)
  refine ⟨hx, fun i => ⟨fun h => ?_, fun h₁ h₂ => ?_, fun h => ?_⟩⟩
  · simpa using bound i true (by simp [h])
  · exact abs_le.mpr ⟨by have hh := bound i false h₁; simp at hh; linarith, by simpa using bound i true h₂⟩
  · have hh := bound i false (by simp [h]); simp at hh; linarith
