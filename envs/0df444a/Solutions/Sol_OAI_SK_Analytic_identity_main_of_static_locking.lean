-- Prove2me | solution 1 for OAI.SK.Analytic.identity_main_of_static_locking
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:02:26.013017+00:00
-- url     : https://prove2.me/submissions/ff83864c-0629-4080-95ff-27a25e59c371

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004

section
-- module Solutions.OAIQ036_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_Basic
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem overlap_comm {n : ℕ} (x y : Config n) : overlap x y = overlap y x := by
  simp only [overlap, mul_comm]

theorem sum_edges {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ e : Edge n, f e.val) = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then f (i, j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by simp) f]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem overlap_self {n : ℕ} (hn : 0 < n) (x : Config n) : overlap x x = 1 := by
  simp only [overlap, ← pow_two, spin_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hn.ne')

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_DisorderPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem continuous_partition {n : ℕ} (β : ℝ) :
    Continuous (partition (n := n) β) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x)))

theorem continuous_gibbs {n : ℕ} (β : ℝ) (x : Config n) :
    Continuous (fun J : Disorder n => gibbs β J x) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_hamiltonian x))).div
    (continuous_partition β) (fun J => ne_of_gt (partition_pos β J))

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem stretchedLogScale_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)^kappa) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num [kappa])).comp tendsto_natCast_atTop_atTop

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathChoice
attribute [-instance] _root_.OAI.SK.disorderLaw_probability _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem discreteKernel_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (k : ℕ) (x y : Config n) :
    0 ≤ discreteKernel β J k x y := by
  induction k generalizing x y with
  | zero => simp only [discreteKernel]; split_ifs <;> norm_num
  | succ k ih =>
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (heatBath_nonneg β J x z) (ih z y))

theorem discreteKernel_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (k : ℕ) (x : Config n) :
    ∑ y : Config n, discreteKernel β J k x y = 1 := by
  classical
  induction k generalizing x with
  | zero => simp [discreteKernel]
  | succ k ih =>
    simp only [discreteKernel]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,ih,mul_one]
    exact heatBath_sum hn β J x

theorem discreteKernel_le_one {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (k : ℕ) (x y : Config n) : discreteKernel β J k x y ≤ 1 := by
  rw [← discreteKernel_sum hn β J k x]
  exact Finset.single_le_sum (fun z _ => discreteKernel_nonneg β J k x z) (Finset.mem_univ y)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathEnergy
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem coupling_comm {n : ℕ} (J : Disorder n) (i j : Fin n) : coupling J i j = coupling J j i := by
  rcases lt_trichotomy i j with h | h | h
  · simp [coupling,h,not_lt_of_ge h.le]
  · subst j; rfl
  · simp [coupling,h,not_lt_of_ge h.le]

theorem interactionSum_eq_edges {n : ℕ} (J : Disorder n) (v : Fin n → ℝ) :
    interactionSum J v = 2*∑ e : Edge n, J e*v e.val.1*v e.val.2 := by
  have hE : (∑ e : Edge n, J e*v e.val.1*v e.val.2) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then coupling J i j*v i*v j else 0 := by
    calc
      _ = ∑ e : Edge n, coupling J e.val.1 e.val.2*v e.val.1*v e.val.2 := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [coupling,dite_eq_left e.property]
      _ = _ := sum_edges (fun p => coupling J p.1 p.2*v p.1*v p.2)
  have ht (i j : Fin n) : coupling J i j*v i*v j =
      (if i < j then coupling J i j*v i*v j else 0)+
      (if j < i then coupling J i j*v i*v j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [h,not_lt_of_ge h.le,ite_true,ite_false,add_zero]
    · subst j; simp
    · simp only [h,not_lt_of_ge h.le,ite_true,ite_false,zero_add]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun j _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun k _ => ht j k))
  unfold interactionSum
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hswap : (∑ i : Fin n, ∑ j : Fin n, if j < i then coupling J i j*v i*v j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then coupling J i j*v i*v j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [coupling_comm J j i]
    split_ifs <;> ring
  rw [hswap,← hE]
  ring

theorem hamiltonian_eq_interactionSum {n : ℕ} (J : Disorder n) (x : Config n) :
    hamiltonian J x = interactionSum J (fun i => spin (x i))/(2*Real.sqrt n) := by
  rw [interactionSum_eq_edges]
  unfold hamiltonian
  ring

theorem interactionSum_update {n : ℕ} (J : Disorder n) (v : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    interactionSum J (Function.update v i r) = interactionSum J v+
      2*(r-v i)*(∑ j, coupling J i j*v j) := by
  classical
  have ht (j k : Fin n) : coupling J j k*Function.update v i r j*Function.update v i r k =
      coupling J j k*v j*v k+
      (if j=i then coupling J i k*(r-v i)*v k else 0)+
      (if k=i then coupling J j i*v j*(r-v i) else 0) := by
    by_cases hj : j=i <;> by_cases hk : k=i
    · subst j; subst k; simp
    · subst j; simp only [Function.update_self,Function.update_of_ne hk,ite_true,ite_eq_right hk,add_zero]; ring
    · subst k; simp only [Function.update_self,Function.update_of_ne hj,ite_true,ite_eq_right hj,add_zero]; ring
    · simp only [Function.update_of_ne hj,Function.update_of_ne hk,ite_false,hj,hk,add_zero]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun j _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun k _ => ht j k))
  unfold interactionSum
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have H1 : (∑ j : Fin n, ∑ k : Fin n, if j=i then coupling J i k*(r-v i)*v k else 0) =
      (r-v i)*(∑ k, coupling J i k*v k) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have H2 : (∑ j : Fin n, ∑ k : Fin n, if k=i then coupling J j i*v j*(r-v i) else 0) =
      (r-v i)*(∑ j, coupling J i j*v j) := by
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [coupling_comm J j i]
    ring
  rw [H1,H2]
  ring

theorem hamiltonian_update {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    hamiltonian J (Function.update x i b) = hamiltonian J x+
      (spin b-spin (x i))*localField J x i := by
  have hu : (fun j => spin (Function.update x i b j)) =
      Function.update (fun j => spin (x j)) i (spin b) := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [Function.update_of_ne h]
  rw [hamiltonian_eq_interactionSum,hu,interactionSum_update,hamiltonian_eq_interactionSum]
  unfold localField
  ring

theorem localField_update {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    localField J (Function.update x i b) i = localField J x i := by
  unfold localField
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=i
  · subst j; simp
  · simp only [Function.update_of_ne h]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathStationary
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem update_reversible {n : ℕ} (x y : Config n) (i : Fin n)
    (h : Function.update x i (y i) = y) : Function.update y i (x i) = x := by
  classical
  funext j
  by_cases hj : j=i
  · subst j; simp
  · have H := congrFun h j
    simpa only [Function.update_of_ne hj] using H.symm

theorem siteChoice_detailedBalance {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) (i : Fin n)
    (h : Function.update x i (y i) = y) :
    gibbs β J x*siteChoice β J x i (y i) = gibbs β J y*siteChoice β J y i (x i) := by
  have hF : localField J y i = localField J x i := by
    rw [← h]
    exact localField_update J x i (y i)
  have hH : hamiltonian J y = hamiltonian J x+(spin (y i)-spin (x i))*localField J x i := by
    simpa only [h] using hamiltonian_update J x i (y i)
  have he : Real.exp (β*hamiltonian J x)*Real.exp (β*spin (y i)*localField J x i) =
      Real.exp (β*hamiltonian J y)*Real.exp (β*spin (x i)*localField J x i) := by
    rw [← Real.exp_add,← Real.exp_add,hH]
    congr 1
    ring
  unfold gibbs siteChoice
  rw [hF,div_mul_div_comm,div_mul_div_comm,he]

theorem heatBath_detailedBalance {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    gibbs β J x*heatBath β J x y = gibbs β J y*heatBath β J y x := by
  classical
  unfold heatBath
  rw [← mul_div_assoc,← mul_div_assoc,Finset.mul_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Function.update x i (y i) = y
  · have hr := update_reversible x y i h
    simp only [ite_eq_left h,ite_eq_left hr]
    exact siteChoice_detailedBalance β J x y i h
  · have hr : Function.update y i (x i) ≠ x := fun hy => h (update_reversible y x i hy)
    simp only [ite_eq_right h,ite_eq_right hr,mul_zero]

theorem heatBath_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (y : Config n) :
    ∑ x : Config n, gibbs β J x*heatBath β J x y = gibbs β J y := by
  simp_rw [heatBath_detailedBalance]
  rw [← Finset.mul_sum,heatBath_sum hn,mul_one]

theorem overlap_update_le {n : ℕ} (hn : 0 < n) (v x : Config n) (i : Fin n) (b : Bool) :
    |overlap v (Function.update x i b)-overlap v x| ≤ 2/(n:ℝ) := by
  classical
  have H : (∑ j : Fin n, spin (v j)*spin (Function.update x i b j)) =
      (∑ j : Fin n, spin (v j)*spin (x j))+spin (v i)*(spin b-spin (x i)) := by
    have ht (j : Fin n) : spin (v j)*spin (Function.update x i b j) =
        spin (v j)*spin (x j)+(if j=i then spin (v i)*(spin b-spin (x i)) else 0) := by
      by_cases hj : j=i
      · subst j; simp only [Function.update_self,ite_true]; ring
      · simp only [Function.update_of_ne hj,ite_eq_right hj,add_zero]
    simp_rw [ht]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hb : |spin (v i)*(spin b-spin (x i))| ≤ 2 := by
    cases hv : v i <;> cases hx : x i <;> cases b <;> norm_num [spin,hv,hx]
  unfold overlap
  rw [H,add_div,add_sub_cancel_left,abs_div,abs_of_pos (show 0 < (n:ℝ) by exact_mod_cast hn)]
  exact div_le_div_of_nonneg_right hb (by positivity)

theorem heatBath_overlap_step {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (v x y : Config n)
    (hxy : 0 < heatBath β J x y) : |overlap v y-overlap v x| ≤ 2/(n:ℝ) := by
  classical
  by_contra h
  have hz : heatBath β J x y = 0 := by
    unfold heatBath
    have HH : ∀ i : Fin n, Function.update x i (y i) ≠ y := by
      intro i hi
      exact h (hi ▸ overlap_update_le hn v x i (y i))
    simp only [HH,ite_false,Finset.sum_const_zero,zero_div]
  linarith

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_FiniteMarkovPath
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
namespace FiniteMarkov
variable {X : Type*}

theorem pathWeight_first [Fintype X] (p : X → ℝ) (K : X → X → ℝ)
    (hK : ∀ x,∑ y,K x y=1) (m : ℕ) (f : X → ℝ) :
    (∑ s : Fin (m+1) → X,pathWeight p K m s*f (s 0))=∑ x,p x*f x := by
  rw [sum_cons]
  simp only [pathWeight,Fin.cons_zero,Fin.tail_cons,mul_right_comm (p _) _ (f _),← Finset.mul_sum,
    walkWeight_sum K hK,mul_one]

theorem pathWeight_marginal [Fintype X] (p : X → ℝ) (K : X → X → ℝ)
    (hK : ∀ x,∑ y,K x y=1) (hstat : ∀ y,∑ x,p x*K x y=p y)
    (m : ℕ) (k : Fin (m+1)) (f : X → ℝ) :
    (∑ s : Fin (m+1) → X,pathWeight p K m s*f (s k))=∑ y,p y*f y := by
  classical
  induction m with
  | zero =>
    have hk : k=0 := by exact Fin.ext (by omega)
    subst k
    exact pathWeight_first p K hK 0 f
  | succ m ih =>
    refine Fin.cases (pathWeight_first p K hK (m+1) f) (fun k => ?_) k
    rw [sum_cons]
    simp only [pathWeight,Fin.cons_zero,Fin.tail_cons,Fin.cons_succ,walkWeight]
    simp_rw [sum_cons m]
    simp only [Fin.cons_zero,Fin.tail_cons]
    have he (x y : X) (s : Fin m → X) :
        p x*(K x y*walkWeight K m y s)*f ((Fin.cons y s : Fin (m+1) → X) k)=
        (p x*K x y)*(walkWeight K m y s*f ((Fin.cons y s : Fin (m+1) → X) k)) := by ring
    simp_rw [he,← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hstat]
    have HH := ih k
    rw [sum_cons] at HH
    simpa only [pathWeight,Fin.cons_zero,Fin.tail_cons,mul_assoc,← Finset.mul_sum] using HH

theorem walkWeight_pos_step (K : X → X → ℝ) (hK : ∀ x y,0≤K x y)
    (m : ℕ) (x : X) (s : Fin m → X) (h : 0<walkWeight K m x s) :
    ∀ i : Fin m,0<K ((Fin.cons x s : Fin (m+1) → X) i.castSucc) (s i) := by
  induction m generalizing x with
  | zero => intro i; exact Fin.elim0 i
  | succ m ih =>
    have hfirst : 0<K x (s 0) := lt_of_le_of_ne (hK _ _) (by intro he; simp [walkWeight,← he] at h)
    have htail : 0<walkWeight K m (s 0) (Fin.tail s) := (mul_pos_iff_of_pos_left hfirst).mp h
    intro i
    refine Fin.cases (by simpa using hfirst) (fun i => ?_) i
    simpa only [Fin.castSucc_succ,Fin.cons_succ,Fin.cons_self_tail,Fin.tail] using ih (s 0) (Fin.tail s) htail i

theorem pathWeight_pos_step (p : X → ℝ) (K : X → X → ℝ)
    (hp : ∀ x,0≤p x) (hK : ∀ x y,0≤K x y)
    (m : ℕ) (s : Fin (m+1) → X) (h : 0<pathWeight p K m s) :
    ∀ i : Fin m,0<K (s i.castSucc) (s i.succ) := by
  have hh : 0<walkWeight K m (s 0) (Fin.tail s) :=
    pos_of_mul_pos_right h (hp (s 0))
  intro i
  simpa only [Fin.cons_self_tail,Fin.tail] using walkWeight_pos_step K hK m (s 0) (Fin.tail s) hh i

end FiniteMarkov

theorem stationaryPathWeight_marginal {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    (m : ℕ) (k : Fin (m+1)) (f : Config n → ℝ) :
    (∑ s,stationaryPathWeight β J m s*f (s k))=∑ y,gibbs β J y*f y :=
  FiniteMarkov.pathWeight_marginal _ _ (heatBath_sum hn β J) (heatBath_stationary hn β J) m k f

theorem stationaryPathWeight_pos_jump {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    (m : ℕ) (s : Fin (m+1) → Config n) (hs : 0 < stationaryPathWeight β J m s)
    (v : Config n) (i : Fin m) : |overlap v (s i.succ)-overlap v (s i.castSucc)|≤2/(n:ℝ) :=
  heatBath_overlap_step hn β J v _ _
    (FiniteMarkov.pathWeight_pos_step _ _ (fun x => (gibbs_pos β J x).le) (heatBath_nonneg β J) m s hs i)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteLaw
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

namespace FiniteLaw
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem expect_nonneg (P : FiniteLaw X) {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hf x))

theorem expect_mono (P : FiniteLaw X) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

theorem expect_add (P : FiniteLaw X) (f g : X → ℝ) :
    P.expect (fun x => f x+g x)=P.expect f+P.expect g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

theorem expect_mul_const (P : FiniteLaw X) (f : X → ℝ) (c : ℝ) :
    P.expect (fun x => f x*c)=P.expect f*c := by
  simp only [expect,← mul_assoc,Finset.sum_mul]

theorem expect_const_mul (P : FiniteLaw X) (c : ℝ) (f : X → ℝ) :
    P.expect (fun x => c*f x)=c*P.expect f := by
  simp_rw [mul_comm c]
  exact expect_mul_const P f c

theorem expect_sum (P : FiniteLaw X) {I : Type*} [Fintype I] (f : I → X → ℝ) :
    P.expect (fun x => ∑ i, f i x)=∑ i, P.expect (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

theorem prob_nonneg (P : FiniteLaw X) (E : X → Prop) : 0 ≤ P.prob E :=
  P.expect_nonneg (fun x => by split_ifs <;> norm_num)

theorem prob_le_one (P : FiniteLaw X) (E : X → Prop) : P.prob E ≤ 1 := by
  rw [← P.expect_const 1]
  exact P.expect_mono (fun x => by split_ifs <;> norm_num)

theorem prob_mono (P : FiniteLaw X) {E F : X → Prop} (h : ∀ x, E x → F x) : P.prob E ≤ P.prob F := by
  apply P.expect_mono
  intro x
  by_cases he : E x
  · simp only [ite_eq_left he,ite_eq_left (h x he),le_refl]
  · simp only [ite_eq_right he]; split_ifs <;> norm_num

theorem prob_not (P : FiniteLaw X) (E : X → Prop) : P.prob (fun x => ¬E x)=1-P.prob E := by
  have he : P.prob E+P.prob (fun x => ¬E x)=1 := by
    rw [prob,prob,← expect_add]
    convert P.expect_const 1 using 2
    all_goals try with_reducible_and_instances rfl
    funext x
    by_cases h : E x <;> simp [h]
  linarith only [he]

theorem prob_or (P : FiniteLaw X) (E F : X → Prop) :
    P.prob (fun x => E x ∨ F x) ≤ P.prob E+P.prob F := by
  simp only [prob]
  rw [← expect_add]
  apply P.expect_mono
  intro x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he,hf]

theorem prob_exists (P : FiniteLaw X) {I : Type*} [Fintype I] (E : I → X → Prop) :
    P.prob (fun x => ∃ i, E i x) ≤ ∑ i, P.prob (E i) := by
  simp only [prob]
  rw [← expect_sum]
  apply P.expect_mono
  intro x
  by_cases h : ∃ i, E i x
  · rw [ite_eq_left h]
    obtain ⟨i,hi⟩ := h
    exact (by simpa only [ite_eq_left hi] using
      (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => show 0 ≤ (if E j x then (1:ℝ) else 0) by split_ifs <;> norm_num) (Finset.mem_univ i)))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem prod_expect (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X × Y → ℝ) :
    (P.prod Q).expect f=P.expect (fun x => Q.expect (fun y => f (x,y))) := by
  simp only [expect,prod,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem prod_expect_fst (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X → ℝ) :
    (P.prod Q).expect (fun z => f z.1)=P.expect f := by
  simp only [prod_expect,expect_const]

end FiniteLaw

theorem pathFiniteLaw_marginal {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (m : ℕ) (k : Fin (m+1)) (f : Config n → ℝ) :
    (pathFiniteLaw hn β J m).expect (fun x => f (x k))=(gibbsFiniteLaw β J).expect f :=
  stationaryPathWeight_marginal hn β J m k f

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic.FiniteLaw
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem iid_expect_equiv (P : FiniteLaw X) (e : I ≃ J) (f : (J → X) → ℝ) :
    (P.iid I).expect (fun z => f (z ∘ e.symm))=(P.iid J).expect f := by
  classical
  unfold expect iid pi
  apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl X))
  intro z
  dsimp only [Equiv.arrowCongr_apply,Equiv.coe_refl,Function.comp_def]
  congr 1
  exact (e.symm.prod_comp (fun i => P.weight (z i))).symm

theorem iid_expect_restrict (P : FiniteLaw X) (s : I → Prop)
    (f : ({i // s i} → X) → ℝ) :
    (P.iid I).expect (fun z => f (fun i => z i))=(P.iid {i // s i}).expect f := by
  classical
  let Q := P.iid {i // ¬s i}
  calc
    _ = ((P.iid {i // s i}).prod Q).expect (fun z => f z.1) := by
      unfold expect iid pi prod
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd s (fun _ => X))
      intro z
      change (∏ i, P.weight (z i))*f (fun i => z i) =
        ((∏ i : {i // s i}, P.weight (z i))*(∏ i : {i // ¬s i}, P.weight (z i)))*f (fun i => z i)
      congr 1
      exact (Fintype.prod_subtype_mul_prod_subtype s (fun i => P.weight (z i))).symm
    _ = _ := prod_expect_fst _ _ f

theorem iid_expect_injective (P : FiniteLaw X) (e : J → I) (he : Function.Injective e)
    (f : (J → X) → ℝ) :
    (P.iid I).expect (fun z => f (z ∘ e))=(P.iid J).expect f := by
  classical
  let : Fintype {i // i∈Set.range e} := Subtype.fintype _
  let k := Equiv.ofInjective e he
  have H := P.iid_expect_restrict (fun i => i∈Set.range e) (fun z => f (z ∘ k))
  have H' := P.iid_expect_equiv k.symm f
  apply H.trans
  unfold expect iid pi at H' ⊢
  simp only [Equiv.symm_symm] at H'
  refine Eq.trans ?_ H'
  apply Finset.sum_congr
  · ext z; simp
  · intro z _
    congr 1
    apply Finset.prod_congr
    · ext i; simp
    · intros; rfl

theorem iid_expect_single (P : FiniteLaw X) (i : I) (f : X → ℝ) :
    (P.iid I).expect (fun z => f (z i))=P.expect f := by
  classical
  have H := P.iid_expect_injective (fun _ : Unit => i)
    (fun _ _ _ => Subsingleton.elim _ _) (fun z => f (z ()))
  change (P.iid I).expect (fun z => f ((z ∘ (fun _ : Unit => i)) ())) = _
  rw [H]
  unfold expect iid pi
  simp only [Fintype.prod_unique]
  apply Fintype.sum_equiv (Equiv.funUnique Unit X)
  intro z
  rfl

theorem iid_expect_fin_succ (P : FiniteLaw X) (p : ℕ) (f : (Fin (p+1) → X) → ℝ) :
    (P.iid (Fin (p+1))).expect f=
      (P.iid (Fin p)).expect (fun z => P.expect (fun a => f (Fin.snoc z a))) := by
  classical
  unfold expect iid pi
  calc
    _ = ∑ z : (Fin p → X) × X, (∏ i, P.weight (z.1 i))*P.weight z.2*f (Fin.snoc z.1 z.2) := by
      apply Fintype.sum_equiv ((Fin.snocEquiv (fun _ : Fin (p+1) => X)).symm.trans (Equiv.prodComm _ _))
      intro z
      simp only [Equiv.trans_apply,Equiv.prodComm_apply,Fin.snocEquiv_symm_apply,Prod.swap,Fin.prod_univ_castSucc]
      simp only [Fin.snoc_init_self,Fin.init]
    _ = _ := by simp only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem iid_predictable_bound (P : FiniteLaw X) (E : (j : ℕ) → (Fin j → X) → X → Prop)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hE : ∀ j z, P.prob (E j z) ≤ a j) (p : ℕ) :
    (P.iid (Fin p)).prob (fun z => ∀ i : Fin p,
      E i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) (z i)) ≤ ∏ i : Fin p, a i := by
  classical
  induction p with
  | zero => simp [prob]
  | succ p ih =>
    simp only [prob] at ih ⊢
    rw [iid_expect_fin_succ]
    have H : (P.iid (Fin p)).expect (fun z => P.expect (fun b =>
        if ∀ i : Fin (p+1), E i.val (fun j => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.isLt⟩) (Fin.snoc (α := fun _ : Fin (p+1) => X) z b i)
        then 1 else 0)) ≤
        (P.iid (Fin p)).expect (fun z => (if ∀ i : Fin p,
          E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i) then 1 else 0)*a p) := by
      apply expect_mono
      intro z
      have hpref (b : X) (i : Fin p) :
          (fun j : Fin i.val => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.castSucc.isLt⟩) =
          (fun j : Fin i.val => z ⟨j.val,j.isLt.trans i.isLt⟩) := by
        funext j
        exact Fin.snoc_castSucc (α := fun _ : Fin (p+1) => X) b z ⟨j.val,j.isLt.trans i.isLt⟩
      have hlast (b : X) : (fun j : Fin p => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans (Nat.lt_succ_self p)⟩)=z := by
        funext j
        exact Fin.snoc_castSucc (α := fun _ : Fin (p+1) => X) b z j
      have heq (b : X) : (∀ i : Fin (p+1),
          E i.val (fun j => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.isLt⟩) (Fin.snoc (α := fun _ : Fin (p+1) => X) z b i)) ↔
          (∀ i : Fin p, E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i)) ∧ E p z b := by
        rw [Fin.forall_iff_castSucc, and_comm]
        constructor
        · intro h
          constructor
          · intro i
            simpa only [Fin.val_castSucc,Fin.snoc_castSucc,hpref] using h.1 i
          · simpa only [Fin.val_last,Fin.snoc_last,hlast] using h.2
        · rintro ⟨h,hp⟩
          constructor
          · intro i
            simpa only [Fin.val_castSucc,Fin.snoc_castSucc,hpref] using h i
          · simpa only [Fin.val_last,Fin.snoc_last,hlast] using hp
      simp_rw [heq]
      by_cases hz : ∀ i : Fin p, E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i)
      · simpa [hz,prob] using hE p z
      · simp only [hz,false_and,ite_false,zero_mul,expect_zero,le_refl]
    convert H.trans (show (P.iid (Fin p)).expect (fun z => (if ∀ i : Fin p,
          E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i) then 1 else 0)*a p) ≤ ∏ i : Fin (p+1), a i from by
      rw [expect_mul_const,Fin.prod_univ_castSucc]
      apply mul_le_mul_of_nonneg_right _ (ha p)
      convert ih using 1 <;> first | rfl | (congr 1; funext z; split_ifs <;> rfl)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (congr 1; funext z; congr 1; funext b; split_ifs <;> rfl)

end SK.Analytic.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Classical
namespace SK.Analytic.FiniteLaw
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
theorem expect_indicator_eq_prob (P : FiniteLaw X) (E : X → Prop) [DecidablePred E] :
    P.expect (fun x => if E x then 1 else 0)=P.prob E := by
  unfold prob
  congr 1
  funext x
  split_ifs <;> rfl

theorem iid_prob_single (P : FiniteLaw X) (i : I) (E : X → Prop) :
    (P.iid I).prob (fun z => E (z i))=P.prob E := by
  exact P.iid_expect_single i (fun x => if E x then 1 else 0)

theorem iid_prob_injective (P : FiniteLaw X) (e : J → I) (he : Function.Injective e)
    (E : (J → X) → Prop) :
    (P.iid I).prob (fun z => E (z ∘ e))=(P.iid J).prob E := by
  exact P.iid_expect_injective e he (fun z => if E z then 1 else 0)

end SK.Analytic.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic.FiniteLaw
variable {X Y I J : Type*} [Fintype X] [Fintype Y] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem expect_expect_comm (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X → Y → ℝ) :
    P.expect (fun x => Q.expect (f x))=Q.expect (fun y => P.expect (fun x => f x y)) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem iid_expect_sum (P : FiniteLaw X) (f : (I ⊕ J → X) → ℝ) :
    (P.iid (I ⊕ J)).expect f=(P.iid I).expect (fun z => (P.iid J).expect (fun w => f (Sum.elim z w))) := by
  classical
  unfold expect iid pi
  calc
    _ = ∑ z : (I → X) × (J → X), (∏ i, P.weight (z.1 i))*(∏ j, P.weight (z.2 j))*f (Sum.elim z.1 z.2) := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow I J X)
      intro z
      simp only [Equiv.sumArrowEquivProdArrow_apply_fst,Equiv.sumArrowEquivProdArrow_apply_snd,Fintype.prod_sum_type]
      congr 1
      congr 1
      funext i
      cases i <;> rfl
    _ = _ := by simp only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem iid_miss_bound (P : FiniteLaw X) (A : X → Prop) (K : ℕ) {a : ℝ}
    (_ha : 0 ≤ a) (hA : a ≤ P.prob A) :
    (P.iid (Fin K)).prob (fun z => ∀ i, ¬A (z i)) ≤ Real.exp (-a*K) := by
  have H := P.iid_predictable_bound (fun _ _ x => ¬A x) (fun _ => 1-P.prob A)
    (fun _ => sub_nonneg.mpr (P.prob_le_one A)) (fun _ _ => (P.prob_not A).le) K
  have H' : (P.iid (Fin K)).prob (fun z => ∀ i, ¬A (z i)) ≤ (1-P.prob A)^K := by
    simpa using H
  refine H'.trans ?_
  have hbase : 1-P.prob A ≤ Real.exp (-a) := by
    have H := Real.add_one_le_exp (-a)
    linarith only [H,hA]
  calc
    (1-P.prob A)^K ≤ (Real.exp (-a))^K := pow_le_pow_left₀ (sub_nonneg.mpr (P.prob_le_one A)) hbase K
    _ = Real.exp (-a*K) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem iid_cell_miss_bound (P : FiniteLaw X) (S : X → Prop) (R : X → X → Prop)
    (K : ℕ) {a δ : ℝ} (ha : 0 ≤ a)
    (hcov : P.prob (fun x => S x ∧ P.prob (fun y => S y ∧ R x y)<a) ≤ δ) :
    (P.iid (Fin K)).expect (fun z => P.prob (fun x => S x ∧ ∀ i, ¬(S (z i) ∧ R x (z i)))) ≤
      δ+Real.exp (-a*K) := by
  classical
  unfold prob
  rw [expect_expect_comm]
  calc
    _ ≤ P.expect (fun x => (if S x ∧ P.prob (fun y => S y ∧ R x y)<a then 1 else 0)+Real.exp (-a*K)) := by
      apply expect_mono
      intro x
      by_cases hb : S x ∧ P.prob (fun y => S y ∧ R x y)<a
      · rw [ite_eq_left hb]
        exact (prob_le_one _ _).trans (by linarith only [Real.exp_pos (-a*K)])
      · rw [ite_eq_right hb,zero_add]
        by_cases hx : S x
        · have hmass : a ≤ P.prob (fun y => S y ∧ R x y) := le_of_not_gt (fun h => hb ⟨hx,h⟩)
          simp only [hx,true_and]
          rw [expect_indicator_eq_prob]
          exact P.iid_miss_bound (fun y => S y ∧ R x y) K ha hmass
        · simp only [hx,false_and,ite_false,expect_zero,Real.exp_nonneg]
    _ = P.prob (fun x => S x ∧ P.prob (fun y => S y ∧ R x y)<a)+Real.exp (-a*K) := by
      rw [expect_add,expect_const,expect_indicator_eq_prob]
    _ ≤ _ := by linarith only [hcov]

theorem exists_le_expect (P : FiniteLaw X) (f : X → ℝ) : ∃ x, f x ≤ P.expect f := by
  classical
  by_contra! H
  have he : P.expect f < P.expect f := by
    calc
      P.expect f = ∑ x, P.weight x*P.expect f := by simp only [← Finset.sum_mul,P.sum_one,one_mul]
      _ < ∑ x, P.weight x*f x := by
        apply Finset.sum_lt_sum
        · intro x _
          exact mul_le_mul_of_nonneg_left (H x).le (P.nonneg x)
        · have hp : ∃ x, 0 < P.weight x := by
            by_contra! hp
            have hz : ∑ x, P.weight x=0 := Finset.sum_eq_zero (fun x _ => le_antisymm (hp x) (P.nonneg x))
            rw [P.sum_one] at hz
            norm_num at hz
          obtain ⟨x,hx⟩ := hp
          exact ⟨x,Finset.mem_univ x,mul_lt_mul_of_pos_left (H x) hx⟩
      _ = P.expect f := rfl
  exact lt_irrefl _ he

end SK.Analytic.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic
namespace FiniteLaw
variable {X I A : Type*} [Fintype X] [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

theorem iid_random_cell_miss (P : FiniteLaw X) (K : ℕ) (u : A → I) (v : Fin K → I)
    (he : Function.Injective (Sum.elim u v))
    (C : (A → X) → X → Prop) (R : X → X → Prop) {a δ : ℝ} (ha : 0≤a)
    (hcov : ∀ w, P.prob (fun x => C w x ∧ P.prob (fun y => C w y ∧ R x y)<a) ≤ δ) :
    (P.iid I).expect (fun z => P.prob (fun x => C (z ∘ u) x ∧
      ∀ k, ¬(C (z ∘ u) (z (v k)) ∧ R x (z (v k))))) ≤ δ+Real.exp (-a*K) := by
  classical
  let F (w : A ⊕ Fin K → X) : ℝ := P.prob (fun x => C (w ∘ Sum.inl) x ∧
    ∀ k, ¬(C (w ∘ Sum.inl) (w (Sum.inr k)) ∧ R x (w (Sum.inr k))))
  have H := P.iid_expect_injective (Sum.elim u v) he F
  change (P.iid I).expect (fun z => F (z ∘ Sum.elim u v)) ≤ _
  rw [H,P.iid_expect_sum F]
  calc
    _ ≤ (P.iid A).expect (fun _ => δ+Real.exp (-a*K)) := by
      apply expect_mono
      intro w
      exact P.iid_cell_miss_bound (C w) R K ha (hcov w)
    _ = _ := expect_const _ _
end FiniteLaw

theorem bankJointIndex_injective {p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p))
    (j : Fin p) (hj : j∉pred j) (T : BankTuple K pred j) :
    Function.Injective (bankJointIndex K pred j T) := by
  intro a b H
  cases a with
  | inl i =>
    cases b with
    | inl k =>
      have he : i.val=k.val := congrArg Sigma.fst H
      exact congrArg Sum.inl (Subtype.ext he)
    | inr k =>
      have he : i.val=j := congrArg Sigma.fst H
      apply False.elim; apply hj; simpa only [he] using i.property
  | inr i =>
    cases b with
    | inl k =>
      have he : j=k.val := congrArg Sigma.fst H
      apply False.elim; apply hj; simpa only [← he] using k.property
    | inr k =>
      have he : HEq i k := (Sigma.mk.inj_iff.mp H).2
      exact congrArg Sum.inr (eq_of_heq he)

theorem expected_bank_coverage_bad {n p : ℕ} (P : FiniteLaw (Config n)) (K : Fin p → ℕ)
    (pred : Fin p → Finset (Fin p)) (hpred : ∀ j, j∉pred j) (t q : ℝ) (a δ : Fin p → ℝ)
    (ha : ∀ j,0≤a j)
    (hcov : ∀ j, ∀ w : BankPrior pred j → Config n,
      P.prob (fun x => (∀i,|overlap (w i) x|≤3*t) ∧
        P.prob (fun y => (∀i,|overlap (w i) y|≤3*t) ∧ q≤|overlap x y|)<a j)≤δ j) :
    (P.iid (BankIndex K)).expect (fun z => P.prob (bankCoverageBad K pred t q z)) ≤
      ∑ j, Fintype.card (BankTuple K pred j)*(δ j+Real.exp (-(a j)*(K j))) := by
  classical
  calc
    _ ≤ (P.iid (BankIndex K)).expect (fun z => ∑ j : Fin p, ∑ T : BankTuple K pred j,
        P.prob (fun x => bankCell K pred t z j T x ∧
          ∀ a : Fin (K j), ¬(bankCell K pred t z j T (z ⟨j,a⟩) ∧ q≤|overlap x (z ⟨j,a⟩)|))) := by
      apply FiniteLaw.expect_mono
      intro z
      refine (P.prob_exists _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      exact P.prob_exists _
    _ = ∑ j : Fin p, ∑ T : BankTuple K pred j, (P.iid (BankIndex K)).expect (fun z =>
        P.prob (fun x => bankCell K pred t z j T x ∧
          ∀ a : Fin (K j), ¬(bankCell K pred t z j T (z ⟨j,a⟩) ∧ q≤|overlap x (z ⟨j,a⟩)|))) := by
      rw [FiniteLaw.expect_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact FiniteLaw.expect_sum _ _
    _ ≤ ∑ j : Fin p, ∑ _T : BankTuple K pred j, (δ j+Real.exp (-(a j)*(K j))) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro T _
      exact P.iid_random_cell_miss (I := BankIndex K) (A := BankPrior pred j) (K j) (fun i : BankPrior pred j => (⟨i.val,T i⟩ : BankIndex K)) (fun b => (⟨j,b⟩ : BankIndex K))
        (bankJointIndex_injective K pred j (hpred j) T) (fun w x => ∀i,|overlap (w i) x|≤3*t)
        (fun x y => q≤|overlap x y|) (ha j) (hcov j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_RestrictedConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem replicaGibbsMass_nonneg {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    0 ≤ replicaGibbsMass β J S :=
  Finset.sum_nonneg (fun s _ => Finset.prod_nonneg (fun a _ => (gibbs_pos β J (s a)).le))

theorem replicaGibbsMass_le_one {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J S ≤ 1 := by
  have H : replicaGibbsMass β J S ≤ ∑ s : ReplicaConfig n d, ∏ a, gibbs β J (s a) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun s _ _ => Finset.prod_nonneg (fun a _ => (gibbs_pos β J (s a)).le))
  rw [← Fintype.prod_sum] at H
  simpa only [gibbs_sum,Finset.prod_const_one] using H

theorem continuous_replicaGibbsMass {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) :
    Continuous (fun J : Disorder n => replicaGibbsMass β J S) := by
  apply continuous_finsetSum
  intro s _
  exact continuous_finsetProd _ (fun a _ => continuous_gibbs β (s a))

theorem replicaGibbsMass_integrable {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) :
    Integrable (fun J : Disorder n => replicaGibbsMass β J S) (disorderLaw n) := by
  apply (integrable_const (1:ℝ)).mono' (continuous_replicaGibbsMass β S).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs,abs_of_nonneg (replicaGibbsMass_nonneg β J S)] using
    replicaGibbsMass_le_one β J S

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

namespace FiniteLaw
variable {X I : Type*} [Fintype X] [Fintype I] [DecidableEq I]
theorem iid_expect_involutions (P : FiniteLaw X) (T : I → X → X)
    (hT : ∀ i, Function.Involutive (T i)) (hP : ∀ i x, P.weight (T i x)=P.weight x)
    (f : (I → X) → ℝ) :
    (P.iid I).expect (fun z => f (fun i => T i (z i)))=(P.iid I).expect f := by
  let e : (I → X) ≃ (I → X) :=
    ⟨fun z i => T i (z i),fun z i => T i (z i),fun z => funext (fun i => hT i (z i)),fun z => funext (fun i => hT i (z i))⟩
  unfold expect iid pi
  apply Fintype.sum_equiv e
  intro z
  dsimp only [e,Equiv.coe_fn_mk]
  simp only [hP]

theorem iid_two_then_one (P : FiniteLaw X) (a b : I) (hab : a≠b) (f : (Fin 3 → X) → ℝ) :
    (P.iid I).expect (fun z => P.expect (fun x => f ![z a,z b,x]))=(P.iid (Fin 3)).expect f := by
  classical
  have hi : Function.Injective (![a,b] : Fin 2 → I) := by
    intro i j H
    fin_cases i <;> fin_cases j <;> simp_all
  have H := P.iid_expect_injective (![a,b] : Fin 2 → I) hi
    (fun z => P.expect (fun x => f ![z 0,z 1,x]))
  calc
    _ = (P.iid (Fin 2)).expect (fun z => P.expect (fun x => f ![z 0,z 1,x])) := H
    _ = _ := by
      rw [iid_expect_fin_succ P 2]
      congr 1
      funext z
      congr 1
      funext x
      congr 1
      funext i
      fin_cases i <;> simp [Fin.snoc]
end FiniteLaw

@[simp] theorem overlap_orient_abs {n : ℕ} (ε : Bool) (x y : Config n) :
    |overlap (orient ε x) y|=|overlap x y| := by
  cases ε
  · simp [orient]
  · change |overlap (flip x) y| = |overlap x y|
    rw [overlap_comm,overlap_flip_right,abs_neg,overlap_comm]

theorem iid_gibbs_replica {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    ((gibbsFiniteLaw β J).iid (Fin d)).prob (fun z => z∈S)=replicaGibbsMass β J S := by
  classical
  unfold FiniteLaw.prob FiniteLaw.expect FiniteLaw.iid FiniteLaw.pi gibbsFiniteLaw replicaGibbsMass
  simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem iid_gibbs_oriented_replica {n d : ℕ} (β : ℝ) (J : Disorder n)
    (ε : Fin d → Bool) (S : Finset (ReplicaConfig n d)) :
    ((gibbsFiniteLaw β J).iid (Fin d)).prob (fun z => (fun i => orient (ε i) (z i))∈S)=replicaGibbsMass β J S := by
  have H := (gibbsFiniteLaw β J).iid_expect_involutions (fun i => orient (ε i)) (fun i => orient_orient (ε i))
    (fun i z => gibbs_orient β J (ε i) z) (fun z => if z∈S then 1 else 0)
  simp only [FiniteLaw.expect_indicator_eq_prob] at H
  exact H.trans (iid_gibbs_replica β J S)

theorem bank_triple_oriented {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (a b c : I) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (ε₀ ε₁ ε₂ : Bool) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).prob (fun z => (![orient ε₀ (z a),orient ε₁ (z b),orient ε₂ (z c)] : ReplicaConfig n 3)∈S)=
      replicaGibbsMass β J S := by
  classical
  have hi : Function.Injective (![a,b,c] : Fin 3 → I) := by
    intro i j H
    fin_cases i <;> fin_cases j <;> simp_all
  have H := (gibbsFiniteLaw β J).iid_prob_injective (![a,b,c] : Fin 3 → I) hi
    (fun z => (fun i => orient (![ε₀,ε₁,ε₂] i) (z i))∈S)
  have he (z : I → Config n) : (fun i => orient (![ε₀,ε₁,ε₂] i) ((z ∘ ![a,b,c]) i))=
      (![orient ε₀ (z a),orient ε₁ (z b),orient ε₂ (z c)] : ReplicaConfig n 3) := by
    funext i; fin_cases i <;> rfl
  simp only [he] at H
  exact H.trans (iid_gibbs_oriented_replica β J _ S)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

theorem iid_gibbs_oriented_permuted_replica {n d : ℕ} (β : ℝ) (J : Disorder n)
    (ε : Fin d → Bool) (e : Equiv.Perm (Fin d)) (S : Finset (ReplicaConfig n d)) :
    ((gibbsFiniteLaw β J).iid (Fin d)).prob (fun z => (fun i => orient (ε i) (z (e i)))∈S)=replicaGibbsMass β J S := by
  have H := (gibbsFiniteLaw β J).iid_expect_equiv e.symm
    (fun z => if (fun i => orient (ε i) (z i))∈S then 1 else 0)
  simp only [Equiv.symm_symm,Function.comp_def,FiniteLaw.expect_indicator_eq_prob] at H
  exact H.trans (iid_gibbs_oriented_replica β J ε S)

theorem bank_pair_vertex_permuted {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (a b : I) (hab : a≠b)
    (ε : Fin 3 → Bool) (e : Equiv.Perm (Fin 3)) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).expect (fun z => (gibbsFiniteLaw β J).prob (fun x =>
      (fun i => orient (ε i) ((![z a,z b,x] : ReplicaConfig n 3) (e i)))∈S))=
      replicaGibbsMass β J S := by
  have H := (gibbsFiniteLaw β J).iid_two_then_one a b hab
    (fun z => if (fun i => orient (ε i) (z (e i)))∈S then 1 else 0)
  simp only [FiniteLaw.expect_indicator_eq_prob] at H
  exact H.trans (iid_gibbs_oriented_permuted_replica β J ε e S)

namespace FiniteLaw
variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]
theorem expect_prob_exists_le (P : FiniteLaw X) (Q : FiniteLaw Y) (E : A → X → Y → Prop) :
    P.expect (fun x => Q.prob (fun y => ∃ a,E a x y)) ≤ ∑ a, P.expect (fun x => Q.prob (E a x)) := by
  rw [← P.expect_sum]
  exact P.expect_mono (fun x => Q.prob_exists (fun a y => E a x y))
end FiniteLaw

theorem bankTripleBad_prob {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (level : I → ℕ) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).prob (bankTripleBad level S) ≤
      8*(Fintype.card I:ℝ)^3*replicaGibbsMass β J S := by
  classical
  refine (FiniteLaw.prob_exists _ _).trans ?_
  calc
    _ ≤ ∑ _v : I × I × I × (Fin 3 → Bool), replicaGibbsMass β J S := by
      apply Finset.sum_le_sum
      rintro ⟨a,b,c,ε⟩ _
      by_cases h : level a≠level b ∧ level a≠level c ∧ level b≠level c
      · refine (FiniteLaw.prob_mono _ (fun z hz => hz.2)).trans ?_
        exact (bank_triple_oriented β J a b c
          (fun he => h.1 (congrArg level he)) (fun he => h.2.1 (congrArg level he)) (fun he => h.2.2 (congrArg level he))
          (ε 0) (ε 1) (ε 2) S).le
      · simp only [h,false_and,FiniteLaw.prob_false]
        exact replicaGibbsMass_nonneg β J S
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]; ring

theorem expected_bankVertexBad {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (level : I → ℕ) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).expect (fun z => (gibbsFiniteLaw β J).prob (bankVertexBad level S z)) ≤
      48*(Fintype.card I:ℝ)^2*replicaGibbsMass β J S := by
  classical
  refine (FiniteLaw.expect_prob_exists_le _ _ _).trans ?_
  calc
    _ ≤ ∑ _v : I × I × (Fin 3 → Bool) × Equiv.Perm (Fin 3), replicaGibbsMass β J S := by
      apply Finset.sum_le_sum
      rintro ⟨a,b,ε,e⟩ _
      by_cases h : level a≠level b
      · refine ((gibbsFiniteLaw β J).iid I).expect_mono (fun z => (gibbsFiniteLaw β J).prob_mono (fun x hx => hx.2)) |>.trans ?_
        exact (bank_pair_vertex_permuted β J a b (fun he => h (congrArg level he)) ε e S).le
      · simp only [h,false_and,FiniteLaw.prob_false,FiniteLaw.expect_const]
        exact replicaGibbsMass_nonneg β J S
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Fintype.card_perm,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]; norm_num [Nat.factorial]; ring_nf; simp

theorem exists_fixed_good_bank {n p : ℕ} (β : ℝ) (J : Disorder n) (K : Fin p → ℕ)
    (pred : Fin p → Finset (Fin p)) (hpred : ∀ j, j∉pred j) (t q : ℝ) (a δ : Fin p → ℝ)
    (ha : ∀ j,0≤a j) (S : Finset (ReplicaConfig n 3))
    (hcov : ∀ j, ∀ w : BankPrior pred j → Config n,
      (gibbsFiniteLaw β J).prob (fun x => (∀i,|overlap (w i) x|≤3*t) ∧
        (gibbsFiniteLaw β J).prob (fun y => (∀i,|overlap (w i) y|≤3*t) ∧ q≤|overlap x y|)<a j)≤δ j)
    (E : ℝ)
    (hE : (8*(Fintype.card (BankIndex K):ℝ)^3+48*(Fintype.card (BankIndex K):ℝ)^2)*replicaGibbsMass β J S+
      (∑ j, Fintype.card (BankTuple K pred j)*(δ j+Real.exp (-(a j)*(K j)))) ≤ E)
    (hE1 : E<1) :
    ∃ z : BankIndex K → Config n,
      ¬bankTripleBad (fun i : BankIndex K => i.1.val) S z ∧
      (gibbsFiniteLaw β J).prob (fun x => bankCoverageBad K pred t q z x ∨
        bankVertexBad (fun i : BankIndex K => i.1.val) S z x) ≤ E := by
  classical
  let P := gibbsFiniteLaw β J
  let Q := P.iid (BankIndex K)
  let level (i : BankIndex K) := i.1.val
  let V (z : BankIndex K → Config n) (x : Config n) := bankCoverageBad K pred t q z x ∨ bankVertexBad level S z x
  let f (z : BankIndex K → Config n) : ℝ := (if bankTripleBad level S z then 1 else 0)+P.prob (V z)
  have H : Q.expect f ≤ E := by
    rw [show Q.expect f=Q.prob (bankTripleBad level S)+Q.expect (fun z => P.prob (V z)) from by
      dsimp only [f]; rw [FiniteLaw.expect_add,FiniteLaw.expect_indicator_eq_prob]]
    have HV : Q.expect (fun z => P.prob (V z)) ≤
        Q.expect (fun z => P.prob (bankCoverageBad K pred t q z))+Q.expect (fun z => P.prob (bankVertexBad level S z)) := by
      rw [← FiniteLaw.expect_add]
      exact Q.expect_mono (fun z => P.prob_or _ _)
    have HC := expected_bank_coverage_bad P K pred hpred t q a δ ha hcov
    have HT := bankTripleBad_prob β J level S
    have HB := expected_bankVertexBad β J level S
    dsimp only [P,Q] at HC HV ⊢
    nlinarith only [HV,HC,HT,HB,hE]
  obtain ⟨z,hz⟩ := Q.exists_le_expect f
  have hzE : f z≤E := hz.trans H
  have hnot : ¬bankTripleBad level S z := by
    intro hbad
    have H0 := P.prob_nonneg (V z)
    simp only [f,ite_eq_left hbad] at hzE
    linarith only [hzE,hE1,H0]
  refine ⟨z,hnot,?_⟩
  simpa only [f,ite_eq_right hnot,zero_add] using hzE

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankPool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

theorem overlap_orient_right_abs {n : ℕ} (ε : Bool) (x y : Config n) :
    |overlap x (orient ε y)|=|overlap x y| := by
  rw [overlap_comm,overlap_orient_abs,overlap_comm]

theorem exists_orient_overlap {n : ℕ} (x y : Config n) {q : ℝ} (hq : q≤|overlap x y|) :
    ∃ ε : Bool, q≤overlap (orient ε x) y := by
  by_cases h : 0≤overlap x y
  · exact ⟨false,by simpa only [orient,Bool.false_eq_true,ite_false,abs_of_nonneg h] using hq⟩
  · refine ⟨true,?_⟩
    change q≤overlap (flip x) y
    rw [overlap_comm,overlap_flip_right,overlap_comm]
    simpa only [abs_of_neg (lt_of_not_ge h)] using hq

theorem mem_orientedBankPool {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    (j : Fin p) (v : Config n) : v∈orientedBankPool K z j ↔ ∃ a ε, v=orient ε (z ⟨j,a⟩) := by
  simp only [orientedBankPool,Finset.mem_image,Finset.mem_univ,true_and,Prod.exists]
  aesop

theorem flip_mem_orientedBankPool {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    (j : Fin p) {v : Config n} (hv : v∈orientedBankPool K z j) : flip v∈orientedBankPool K z j := by
  obtain ⟨a,ε,rfl⟩ := (mem_orientedBankPool K z j v).mp hv
  apply (mem_orientedBankPool K z j _).mpr
  refine ⟨a,!ε,?_⟩
  cases ε <;> simp [orient]

theorem natBankDefault_mem {n p : ℕ} (K : Fin p → ℕ) (hK : ∀j,0<K j) (z : BankIndex K → Config n) :
    ∀j,natBankDefault K hK z j∈natBankPool K z j := by
  intro j
  unfold natBankDefault natBankPool
  split_ifs with h
  · exact (mem_orientedBankPool K z ⟨j,h⟩ _).mpr ⟨⟨0,hK ⟨j,h⟩⟩,false,rfl⟩
  · exact Finset.mem_singleton_self _

theorem blockPrior_not_self (p B : ℕ) (j : Fin p) : j∉blockPrior p B j := by simp

theorem bank_pool_coverage {n p : ℕ} (K : Fin p → ℕ) (B : ℕ) (z : BankIndex K → Config n)
    (t q : ℝ) (x : Config n) (hx : ¬bankCoverageBad K (blockPrior p B) t q z x)
    (j : ℕ) (hj : j<p) (v : ℕ → Config n) (hv : ∀i<j,v i∈natBankPool K z i)
    (hc : ∀i,j/B*B ≤ i → i<j → |overlap (v i) x|≤3*t) :
    ∃ w∈natBankPool K z j, q≤overlap w x ∧ ∀i,j/B*B ≤ i → i<j → |overlap (v i) w|≤3*t := by
  let jj : Fin p := ⟨j,hj⟩
  have hg (i : BankPrior (blockPrior p B) jj) :
      ∃ a ε, v i.val.val=orient ε (z ⟨i.val,a⟩) := by
    have hij : i.val.val<j := (mem_blockPrior p B i.val jj).mp i.property |>.2
    have H := hv i.val.val hij
    rw [natBankPool,dite_eq_left i.val.isLt] at H
    exact (mem_orientedBankPool K z i.val _).mp H
  choose T ε hT using hg
  have hcell : bankCell K (blockPrior p B) t z jj T x := by
    intro i
    have hi := (mem_blockPrior p B i.val jj).mp i.property
    have H := hc i.val.val hi.1 hi.2
    rw [hT i,overlap_orient_abs] at H
    exact H
  have hfresh : ∃ a : Fin (K jj), bankCell K (blockPrior p B) t z jj T (z ⟨jj,a⟩) ∧ q≤|overlap x (z ⟨jj,a⟩)| := by
    by_contra H
    apply hx
    exact ⟨jj,T,hcell,by simpa only [not_exists] using H⟩
  obtain ⟨a,ha,hq⟩ := hfresh
  rw [overlap_comm] at hq
  obtain ⟨δ,hδ⟩ := exists_orient_overlap (z ⟨jj,a⟩) x hq
  refine ⟨orient δ (z ⟨jj,a⟩),?_,hδ,?_⟩
  · rw [natBankPool,dite_eq_left hj]
    exact (mem_orientedBankPool K z jj _).mpr ⟨a,δ,rfl⟩
  · intro i hil hij
    let ii : BankPrior (blockPrior p B) jj := ⟨⟨i,hij.trans hj⟩,(mem_blockPrior p B _ _).mpr ⟨hil,hij⟩⟩
    have he : v i=orient (ε ii) (z ⟨ii.val,T ii⟩) := hT ii
    rw [he,overlap_orient_abs,overlap_orient_right_abs]
    exact ha ii

theorem bank_pool_no_triple {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    (S : Finset (ReplicaConfig n 3)) (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) S z)
    (i j k : Fin p) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (v w u : Config n) (hv : v∈orientedBankPool K z i) (hw : w∈orientedBankPool K z j) (hu : u∈orientedBankPool K z k) :
    (![v,w,u] : ReplicaConfig n 3)∉S := by
  obtain ⟨a,ε,rfl⟩ := (mem_orientedBankPool K z i v).mp hv
  obtain ⟨b,δ,rfl⟩ := (mem_orientedBankPool K z j w).mp hw
  obtain ⟨c,η,rfl⟩ := (mem_orientedBankPool K z k u).mp hu
  intro H
  apply hz
  refine ⟨(⟨i,a⟩,⟨j,b⟩,⟨k,c⟩,![ε,δ,η]),?_,H⟩
  exact ⟨fun h => hij (Fin.ext h),fun h => hik (Fin.ext h),fun h => hjk (Fin.ext h)⟩

theorem bank_pool_no_vertex {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    (S : Finset (ReplicaConfig n 3)) (x : Config n)
    (hx : ¬bankVertexBad (fun i : BankIndex K => i.1.val) S z x)
    (i j : Fin p) (hij : i≠j) (v w : Config n)
    (hv : v∈orientedBankPool K z i) (hw : w∈orientedBankPool K z j) (e : Equiv.Perm (Fin 3)) :
    ((![v,w,x] : ReplicaConfig n 3) ∘ e)∉S := by
  obtain ⟨a,ε,rfl⟩ := (mem_orientedBankPool K z i v).mp hv
  obtain ⟨b,δ,rfl⟩ := (mem_orientedBankPool K z j w).mp hw
  intro H
  apply hx
  refine ⟨(⟨i,a⟩,⟨j,b⟩,(fun k => (![ε,δ,false] : Fin 3 → Bool) (e k)),e),fun h => hij (Fin.ext h),?_⟩
  have he : (fun k => orient ((![ε,δ,false] : Fin 3 → Bool) k) ((![z ⟨i,a⟩,z ⟨j,b⟩,x] : ReplicaConfig n 3) k)) =
      (![orient ε (z ⟨i,a⟩),orient δ (z ⟨j,b⟩),x] : ReplicaConfig n 3) := by funext k; fin_cases k <;> rfl
  change ((fun k => orient ((![ε,δ,false] : Fin 3 → Bool) k) ((![z ⟨i,a⟩,z ⟨j,b⟩,x] : ReplicaConfig n 3) k)) ∘ e)∈S
  rw [he]
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

 theorem bankPrefix_nonneg (c : ℕ → ℝ) (hc : ∀j,0 ≤ c j) (j : ℕ) : 0≤bankPrefix c j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => simp only [bankPrefix]; linarith only [ih,hc j]

 theorem bankPrefix_mono (c : ℕ → ℝ) (hc : ∀j,0 ≤ c j) : Monotone (bankPrefix c) := by
  apply monotone_nat_of_le_succ
  intro j
  simp only [bankPrefix]
  linarith only [hc j]

 theorem bankPrefix_cost_le (c : ℕ → ℝ) (hc : ∀j,0 ≤ c j) {j B : ℕ} (hj : j<B) : c j+2≤bankPrefix c B := by
  have h := bankPrefix_mono c hc (show j+1≤B by omega)
  simp only [bankPrefix] at h
  linarith only [h,bankPrefix_nonneg c hc j]

 theorem blockPriorEquiv_mod (p B : ℕ) (hB : 0<B) (j : Fin p) (a : Fin (j.val%B)) :
    ((blockPriorEquiv p B j).symm a).val.val%B=a.val := by
  change (j.val/B*B+a.val)%B=a.val
  rw [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt]
  exact a.isLt.trans (Nat.mod_lt _ hB)

 theorem bankPrefix_sum (c : ℕ → ℝ) (j : ℕ) : (∑i∈Finset.range j,(c i+2))=bankPrefix c j := by
  induction j with
  | zero => simp [bankPrefix]
  | succ j ih => rw [Finset.sum_range_succ,ih]; simp only [bankPrefix]; ring

 theorem bankTuple_card_bound {p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (K : Fin p → ℕ) (L : ℝ)
    (hK : ∀j,(K j:ℝ)≤Real.exp ((c (j.val%B)+2)*L)) (j : Fin p) :
    (Fintype.card (BankTuple K (blockPrior p B) j):ℝ)≤Real.exp (bankPrefix c (j.val%B)*L) := by
  have he : (Fintype.card (BankTuple K (blockPrior p B) j):ℝ)=
      ∏i : BankPrior (blockPrior p B) j,(K i.val:ℝ) := by
    simp only [BankTuple,Fintype.card_pi,Fintype.card_fin,Nat.cast_prod]
  rw [he]
  calc
    _ ≤ ∏i : BankPrior (blockPrior p B) j,Real.exp ((c (i.val.val%B)+2)*L) := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _; exact hK i.val
    _ = ∏a : Fin (j.val%B),Real.exp ((c a.val+2)*L) := by
      rw [← Equiv.prod_comp (blockPriorEquiv p B j).symm]
      apply Finset.prod_congr rfl
      intro a _
      rw [blockPriorEquiv_mod p B hB j a]
    _ = Real.exp (bankPrefix c (j.val%B)*L) := by
      rw [← Real.exp_sum,← Finset.sum_mul]
      congr 1
      have hs := Fin.sum_univ_eq_sum_range (fun i => c i+2) (j.val%B)
      rw [hs,bankPrefix_sum]

 theorem bankIndex_card_bound {p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0 ≤ c j)
    (K : Fin p → ℕ) {L : ℝ} (hL : 0≤L)
    (hK : ∀j,(K j:ℝ)≤Real.exp ((c (j.val%B)+2)*L)) :
    (Fintype.card (BankIndex K):ℝ)≤p*Real.exp (bankPrefix c B*L) := by
  simp only [BankIndex,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  calc
    _ ≤ ∑_j : Fin p,Real.exp (bankPrefix c B*L) := by
      apply Finset.sum_le_sum
      intro j _
      exact (hK j).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (bankPrefix_cost_le c hc (Nat.mod_lt _ hB)) hL))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

 theorem ceil_exp_bound {c L : ℝ} (hc : 0 ≤ c) (hL : 1≤L) :
    (⌈Real.exp ((c+1)*L)⌉₊:ℝ)≤Real.exp ((c+2)*L) := by
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos ((c+1)*L)).le
  have he0 : 1≤Real.exp ((c+1)*L) := Real.one_le_exp_iff.mpr (by positivity)
  have he1 : 2≤Real.exp L := by
    have h := Real.add_one_le_exp L
    linarith only [h,hL]
  have he : Real.exp ((c+2)*L)=Real.exp ((c+1)*L)*Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith only [hceil,he0,he1]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_PolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem eventually_const_rpow_le {a b : ℝ} (hab : a<b) (A : ℝ) {B : ℝ} (hB : 0<B) :
    ∀ᶠ n : ℕ in atTop,A*(n:ℝ)^a ≤ B*(n:ℝ)^b := by
  have H := ((tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul A
  have H0 : Tendsto (fun n : ℕ => A*(n:ℝ)^(a-b)) atTop (𝓝 0) := by
    simpa only [neg_sub,mul_zero,Function.comp_apply] using H
  filter_upwards [H0.eventually_le_const hB,eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  rw [Real.rpow_sub hp] at hn
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hp b)).mp (by simpa only [mul_div_assoc] using hn)

theorem polynomial_rpow_exp_decay {u c : ℝ} (hu : 0<u) (hc : 0 < c) (d : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^d*Real.exp (-c*(n:ℝ)^u)) atTop (𝓝 0) := by
  have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((d:ℝ)/u) c hc).comp
    ((tendsto_rpow_atTop hu).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hp.le,mul_div_cancel₀ _ (ne_of_gt hu),Real.rpow_natCast]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_PressureGapProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem integral_le_off_exception {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) {A : Set Ω} (hA : MeasurableSet A)
    {r : ℝ} (hr : 0 ≤ r) (h1 : ∀ x, f x ≤ 1)
    (hout : ∀ x ∉ A, f x ≤ r) : ∫ x, f x ∂μ ≤ r+μ.real A := by
  calc
    _ ≤ ∫ x, r+A.indicator (fun _ => (1:ℝ)) x ∂μ := by
      apply integral_mono hf ((integrable_const r).add ((integrable_const (1:ℝ)).indicator hA))
      intro x
      by_cases hx : x ∈ A
      · simp only [Pi.add_apply,Set.indicator_of_mem hx]
        linarith [h1 x]
      · simp only [Pi.add_apply,Set.indicator_of_notMem hx,add_zero]
        exact hout x hx
    _ = _ := by
      rw [integral_add (integrable_const r) ((integrable_const (1:ℝ)).indicator hA),
        integral_const,integral_indicator_const _ hA]
      simp only [probReal_univ,smul_eq_mul,mul_one,one_mul]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

@[simp] theorem tripleR_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleR (replicaFlip 0 s)= -tripleR s := by
  simp only [tripleR,replicaFlip]
  norm_num only [ite_true,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,ite_false]
  rw [overlap_comm (flip (s 0)),overlap_flip_right,
    overlap_comm (flip (s 0)),overlap_flip_right]
  rw [overlap_comm (s 1),overlap_comm (s 2)]
  ring

@[simp] theorem tripleDelta_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleDelta (replicaFlip 0 s)= -tripleDelta s := by
  simp only [tripleDelta,replicaFlip]
  norm_num only [ite_true,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,ite_false]
  rw [overlap_comm (flip (s 0)),overlap_flip_right,
    overlap_comm (flip (s 0)),overlap_flip_right]
  rw [overlap_comm (s 1),overlap_comm (s 2)]
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BackwardBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem backwards_no_annulus (f : ℕ → ℝ) {l u : ℕ} (_hlu : l≤u) (a d : ℝ)
    (hend : |f u|<a)
    (hstep : ∀ k,l≤k → k<u → |f (k+1)-f k|≤d)
    (havoid : ∀ k,l≤k → k≤u → ¬(a≤|f k| ∧ |f k|≤a+d)) :
    ∀ k,l≤k → k≤u → |f k|<a := by
  intro k hlk hku
  induction hku using Nat.decreasingInduction with
  | self => exact hend
  | @of_succ k hku ih =>
    have hs := hstep k hlk hku
    have hh := ih (by omega)
    by_contra h
    apply havoid k hlk hku.le
    refine ⟨le_of_not_gt h,?_⟩
    have ht : |f k|≤|f (k+1)|+|f (k+1)-f k| := by
      have H := abs_add_le (f (k+1)) (-(f (k+1)-f k))
      rw [show f (k+1)+-(f (k+1)-f k)=f k by ring,abs_neg] at H
      exact H
    linarith only [ht,hs,hh]

theorem narrow_first_violation {n : ℕ} (μ : ProbabilityMeasure ℝ)
    (v y w : Config n) (t₀ ρ E d rᵢ rⱼ : ℝ)
    (_ht : 0<t₀) (_hρ : 0<ρ) (hri : rᵢ∈Icc t₀ (2*t₀))
    (hspacing : 3*ρ ≤ rⱼ-rᵢ) (hwidth : ρ^8<t₀/2)
    (hsmall : E+ρ^20+d/2<ρ^8) (hsep : E+ρ^20+3*d/2≤2*ρ)
    (hd : d/2≤ρ^20)
    (hmass : (μ : Measure ℝ).real (Icc (rᵢ-2*ρ^8) (rᵢ+2*ρ^8))≤ρ^4)
    (href : |overlap v w-rᵢ|≤E) (hq : rⱼ-d≤overlap w y)
    (hlo : 2*ρ^20≤|overlap v y-overlap v w|)
    (hhi : |overlap v y-overlap v w|≤2*ρ^20+d) :
    (![v,y,w] : ReplicaConfig n 3)∈narrowLockingSet n μ t₀ ρ := by
  classical
  let r := (overlap v y+overlap v w)/2
  let δ := (overlap v y-overlap v w)/2
  have hδl : ρ^20≤|δ| := by dsimp [δ]; rw [abs_div]; rw [abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith only [hlo]
  have hδh : |δ|≤ρ^20+d/2 := by dsimp [δ]; rw [abs_div]; rw [abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith only [hhi]
  have hrr : |r-rᵢ|≤E+ρ^20+d/2 := by
    have HH := abs_add_le (overlap v w-rᵢ) δ
    have he : r-rᵢ=(overlap v w-rᵢ)+δ := by dsimp [r,δ]; ring
    rw [he]
    linarith only [HH,href,hδh]
  have hrr' : |r-rᵢ|<ρ^8 := hrr.trans_lt hsmall
  have hr : r∈Ioo (t₀/2) (3*t₀) := by
    obtain ⟨h₁,h₂⟩ := abs_lt.mp hrr'
    constructor <;> linarith only [h₁,h₂,hri.1,hri.2,hwidth]
  have hsub : Icc (r-ρ^8) (r+ρ^8) ⊆ Icc (rᵢ-2*ρ^8) (rᵢ+2*ρ^8) := by
    intro z hz
    obtain ⟨h₁,h₂⟩ := abs_lt.mp hrr'
    constructor <;> linarith only [h₁,h₂,hz.1,hz.2]
  have hq' : r+ρ≤overlap y w := by
    rw [overlap_comm y w]
    have hh := (abs_le.mp hrr).2
    linarith only [hq,hspacing,hsep,hh]
  have hm : (μ : Measure ℝ).real (Icc (r-ρ^8) (r+ρ^8))≤ρ^4 :=
    (measureReal_mono hsub).trans hmass
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change r∈Ioo (t₀/2) (3*t₀) ∧ _≤ρ^4 ∧ r+ρ≤overlap y w ∧ ρ^20≤|δ| ∧ |δ|≤2*ρ^20
  exact ⟨hr,hm,hq',hδl,by linarith only [hδh,hd]⟩

theorem narrow_backwards_transfer {n : ℕ} (μ : ProbabilityMeasure ℝ)
    (v w : Config n) (x : ℕ → Config n) (t₀ ρ E d rᵢ rⱼ : ℝ) {l u : ℕ}
    (hlu : l≤u) (ht : 0<t₀) (hρ : 0<ρ) (hri : rᵢ∈Icc t₀ (2*t₀))
    (hspacing : 3*ρ ≤ rⱼ-rᵢ) (hwidth : ρ^8<t₀/2)
    (hsmall : E+ρ^20+d/2<ρ^8) (hsep : E+ρ^20+3*d/2≤2*ρ) (hd : d/2≤ρ^20)
    (hmass : (μ : Measure ℝ).real (Icc (rᵢ-2*ρ^8) (rᵢ+2*ρ^8))≤ρ^4)
    (href : |overlap v w-rᵢ|≤E)
    (hend : |overlap v (x u)-overlap v w|<2*ρ^20)
    (hjump : ∀ k,l≤k → k<u → |overlap v (x (k+1))-overlap v (x k)|≤d)
    (hsearch : ∀ k,l≤k → k≤u → rⱼ-d≤overlap w (x k))
    (havoid : ∀ k,l≤k → k≤u →
      (![v,x k,w] : ReplicaConfig n 3)∉narrowLockingSet n μ t₀ ρ) :
    ∀ k,l≤k → k≤u → |overlap v (x k)-overlap v w|<2*ρ^20 := by
  apply backwards_no_annulus (fun k => overlap v (x k)-overlap v w) hlu (2*ρ^20) d hend
  · intro k hk hku
    simpa only [sub_sub_sub_cancel_right] using hjump k hk hku
  · intro k hk hku ⟨hlo,hhi⟩
    exact havoid k hk hku (narrow_first_violation μ v (x k) w t₀ ρ E d rᵢ rⱼ
      ht hρ hri hspacing hwidth hsmall hsep hd hmass href (hsearch k hk hku) hlo hhi)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_Crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem lastCrossing_le (f : ℕ → ℝ) (r : ℝ) (u : ℕ) : lastCrossing f r u ≤ u :=
  Nat.findGreatest_le u

theorem lastCrossing_spec (f : ℕ → ℝ) (r : ℝ) (u : ℕ)
    (hex : ∃ k ≤ u,f k ≤ r) : f (lastCrossing f r u) ≤ r := by
  obtain ⟨k,hk,h⟩ := hex
  exact Nat.findGreatest_spec (P:=fun k => f k ≤ r) hk h

theorem lastCrossing_after (f : ℕ → ℝ) (r : ℝ) (u k : ℕ)
    (hk : lastCrossing f r u < k) (hku : k ≤ u) : r < f k := by
  exact lt_of_not_ge ((Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest (fun k => f k ≤ r) u = _)).2.2 hk hku)

theorem lastCrossing_band (f : ℕ → ℝ) (r d : ℝ) (u : ℕ)
    (hend : r < f u) (hex : ∃ k ≤ u,f k ≤ r)
    (hjump : ∀ k, k < u → |f (k+1)-f k| ≤ d) :
    f (lastCrossing f r u) ∈ Icc (r-d) r := by
  have hl := lastCrossing_le f r u
  have hs := lastCrossing_spec f r u hex
  have hlt : lastCrossing f r u < u := lt_of_le_of_ne hl (by intro he; rw [he] at hs; linarith)
  have ha := lastCrossing_after f r u (lastCrossing f r u+1) (by omega) (by omega)
  have hj := hjump _ hlt
  exact ⟨by linarith only [ha,(abs_le.mp hj).2],hs⟩

theorem lastCrossing_search (f : ℕ → ℝ) (r d : ℝ) (u : ℕ)
    (hd : 0 ≤ d) (hend : r < f u)
    (hjump : ∀ k, k < u → |f (k+1)-f k| ≤ d) :
    ∀ k,lastCrossing f r u ≤ k → k ≤ u → r-d ≤ f k := by
  intro k hk hku
  by_cases hex : ∃ i ≤ u,f i ≤ r
  · by_cases he : lastCrossing f r u=k
    · rw [← he]; exact (lastCrossing_band f r d u hend hex hjump).1
    · exact (by linarith only [lastCrossing_after f r u k (lt_of_le_of_ne hk he) hku,hd])
  · have h : r < f k := lt_of_not_ge (by intro h; exact hex ⟨k,hku,h⟩)
    linarith only [h,hd]

theorem anchored_backwards_crossing {n : ℕ} (μ : ProbabilityMeasure ℝ)
    (v w : Config n) (x : ℕ → Config n) (t₀ ρ E d rᵢ rⱼ q : ℝ) (u : ℕ)
    (ht : 0 < t₀) (hρ : 0 < ρ) (hri : rᵢ ∈ Icc t₀ (2*t₀))
    (hspacing : 3*ρ ≤ rⱼ-rᵢ) (hwidth : ρ^8 < t₀/2)
    (hsmall : E+ρ^20+d/2 < ρ^8) (hsep : E+ρ^20+3*d/2 ≤ 2*ρ)
    (hd : 0 ≤ d) (hd' : d/2 ≤ ρ^20) (hq : rᵢ+E+2*ρ^20 < q)
    (hmass : (μ : Measure ℝ).real (Icc (rᵢ-2*ρ^8) (rᵢ+2*ρ^8)) ≤ ρ^4)
    (href : |overlap v w-rᵢ| ≤ E)
    (hanchor : q ≤ overlap v (x 0)) (_htarget : rⱼ < overlap w (x u))
    (hend : |overlap v (x u)-overlap v w| < 2*ρ^20)
    (hjump : ∀ z k, k < u → |overlap z (x (k+1))-overlap z (x k)| ≤ d)
    (havoid : ∀ k, k ≤ u → (![v,x k,w] : ReplicaConfig n 3)∉narrowLockingSet n μ t₀ ρ) :
    ∃ k ≤ u,overlap w (x k) ≤ rⱼ := by
  by_contra H
  have hs : ∀ k,0 ≤ k → k ≤ u → rⱼ-d ≤ overlap w (x k) := by
    intro k _ hk
    have hh : rⱼ < overlap w (x k) := lt_of_not_ge (fun hh => H ⟨k,hk,hh⟩)
    linarith only [hh,hd]
  have HH := narrow_backwards_transfer μ v w x t₀ ρ E d rᵢ rⱼ (Nat.zero_le u)
    ht hρ hri hspacing hwidth hsmall hsep hd' hmass href hend
    (fun k _ hk => hjump v k hk) hs (fun k _ hk => havoid k hk) 0 (by omega) (by omega)
  linarith only [(abs_lt.mp HH).2,(abs_le.mp href).2,hanchor,hq]

theorem firstCrossing_band (f : ℕ → ℝ) (r d : ℝ) (m : ℕ)
    (hstart : r < f 0) (hend : f m ≤ r)
    (hjump : ∀ k, k < m → |f (k+1)-f k| ≤ d) :
    firstCrossing f r m ≤ m ∧ f (firstCrossing f r m) ∈ Icc (r-d) r := by
  have hex : ∃ k, k ≤ m ∧ f k ≤ r := ⟨m,le_rfl,hend⟩
  rw [firstCrossing,dite_eq_left hex]
  have hs := Nat.find_spec hex
  have hz : 0 < Nat.find hex := by
    by_contra H
    have he : Nat.find hex=0 := by omega
    rw [he] at hs
    linarith only [hs.2,hstart]
  have hp : r < f (Nat.find hex-1) := by
    apply lt_of_not_ge
    intro h
    exact Nat.find_min hex (by omega : Nat.find hex-1 < Nat.find hex) ⟨by omega,h⟩
  have hj := hjump (Nat.find hex-1) (by omega)
  rw [Nat.sub_add_cancel hz] at hj
  exact ⟨hs.1,by linarith only [hp,(abs_le.mp hj).1],hs.2⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GreedyRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem greedyRun_predictable {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r s : ℕ → ℝ) (b : ℝ) (m j : ℕ)
    (h : ∀ i < j, r i=s i) : greedyRun base pick x r b m j=greedyRun base pick x s b m j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := ih (fun i hi => h i (by omega))
    simp only [greedyRun,hp,h j (by omega)]

theorem greedyReference_predictable {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r s : ℕ → ℝ) (b : ℝ) (m j : ℕ)
    (h : ∀ i < j, r i=s i) : greedyReference base pick x r b m j=greedyReference base pick x s b m j := by
  unfold greedyReference
  rw [greedyRun_predictable base pick x r s b m j h]

theorem greedyRun_refs {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r : ℕ → ℝ) (b : ℝ) (m j i : ℕ) (hi : i < j) :
    (greedyRun base pick x r b m j).refs i=greedyReference base pick x r b m i := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : i=j
    · subst i
      simp only [greedyRun,Function.update_self]
      rfl
    · simpa only [greedyRun,Function.update_of_ne he] using ih (by omega)

theorem greedyRun_range {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r : ℕ → ℝ) (b : ℝ) (m j : ℕ) :
    ∀ i ∈ (greedyRun base pick x r b m j).kept, i < j := by
  induction j with
  | zero => simp [greedyRun]
  | succ j ih =>
    intro i hi
    simp only [greedyRun,Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · omega
    · have := ih i (Finset.mem_sdiff.mp hi).1
      omega

theorem bankPick_mem {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (hf : ∀ j, fallback j ∈ pool j) (B : ℕ) (x : ℕ → Config n) (t q : ℝ)
    (j : ℕ) (v : ℕ → Config n) (u : ℕ) : bankPick pool fallback B x t q j v u ∈ pool j := by
  unfold bankPick
  split_ifs with h
  · exact h.choose_spec.1
  · exact hf j

theorem bankPick_spec {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (B : ℕ) (x : ℕ → Config n) (t q : ℝ)
    (j : ℕ) (v : ℕ → Config n) (u : ℕ)
    (h : ∃ w ∈ pool j, q ≤ overlap w (x u) ∧
      ∀ i, j/B*B ≤ i → i < j → |overlap (v i) w| ≤ 3*t) :
    q ≤ overlap (bankPick pool fallback B x t q j v u) (x u) ∧
      ∀ i, j/B*B ≤ i → i < j → |overlap (v i) (bankPick pool fallback B x t q j v u)| ≤ 3*t := by
  rw [bankPick,dite_eq_left h]
  exact h.choose_spec.2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ProtectedBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem retainedSuffix_empty_of_last {A D : Finset ℕ} {j : ℕ}
    (hD : IsRetainedSuffix A D) (hA : ∀ i ∈ A,i ≤ j) (hj : j ∈ A) (hcompat : j ∉ D) :
    D=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact hcompat (hD.2 hi hj (hA i (hD.1 hi)))

theorem retainedSuffix_preserves_before_block {A D : Finset ℕ} {s B H : ℕ}
    (hD : IsRetainedSuffix A D) (hcard : D.card ≤ H) (hHB : H < B)
    (hblock : Finset.Ico s (s+B) ⊆ A) {i : ℕ} (hi : i ∈ A) (his : i ≤ s) :
    i ∈ A\D := by
  refine Finset.mem_sdiff.mpr ⟨hi,?_⟩
  intro hid
  have hsub : Finset.Ico s (s+B) ⊆ D := by
    intro k hk
    exact hD.2 hid (hblock hk) (his.trans (Finset.mem_Ico.mp hk).1)
  have h := Finset.card_le_card hsub
  rw [Nat.card_Ico] at h
  omega

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_OverlapPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem finite_unit_packing {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [DecidableEq I] (S : Finset I) (u : I → E) (w : E) (b e : ℝ)
    (hb : 0<b) (he : 0≤e) (heb : e<b^2/2)
    (hw : ⟪w,w⟫_ℝ=1) (hu : ∀ i∈S,⟪u i,u i⟫_ℝ=1)
    (hpair : ∀ i∈S,∀ j∈S,i≠j → ⟪u i,u j⟫_ℝ≤e)
    (hlarge : ∀ i∈S,b<⟪u i,w⟫_ℝ) : (S.card:ℝ)<2/b^2 := by
  by_cases hS : S.Nonempty
  · let d : ℝ := S.card
    have hd : 0<d := by dsimp [d]; exact_mod_cast hS.card_pos
    have hl : d*b<⟪∑ i∈S,u i,w⟫_ℝ := by
      rw [sum_inner]
      simpa [d] using Finset.sum_lt_sum_of_nonempty hS hlarge
    have hu' : ⟪∑ i∈S,u i,∑ i∈S,u i⟫_ℝ≤d+d^2*e := by
      rw [sum_inner]
      simp_rw [inner_sum]
      calc
        _ ≤ ∑ i∈S,∑ j∈S,((if i=j then (1:ℝ) else 0)+e) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          by_cases hij : i=j
          · subst j; rw [ite_eq_left rfl,hu i hi]; linarith only [he]
          · simpa only [ite_eq_right hij,zero_add] using hpair i hi j hj hij
        _ = _ := by
          simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.sum_const,nsmul_eq_mul]
          simp only [Finset.sum_ite_mem,Finset.inter_self]
          simp [d]
          ring
    have hcs := real_inner_mul_inner_self_le (∑ i∈S,u i) w
    rw [hw,mul_one] at hcs
    have hls : (d*b)^2<⟪∑ i∈S,u i,w⟫_ℝ^2 := by
      exact pow_lt_pow_left₀ hl (mul_nonneg hd.le hb.le) (by decide)
    have hquad : d^2*b^2<d+d^2*e := by nlinarith only [hls,hcs,hu']
    have hdb : d*b^2<2 := by
      by_contra h
      have hd2 : 2≤d*b^2 := le_of_not_gt h
      have hpos : 0<d^2 := sq_pos_of_pos hd
      have hs := mul_lt_mul_of_pos_left heb hpos
      have hm := mul_le_mul_of_nonneg_left hd2 hd.le
      nlinarith only [hquad,hs,hm]
    exact (lt_div_iff₀ (sq_pos_of_pos hb)).mpr (by simpa [d] using hdb)
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hz,Finset.card_empty,Nat.cast_zero]
    positivity

theorem spinUnitVector_inner {n : ℕ} (x y : Config n) :
    ⟪spinUnitVector x,spinUnitVector y⟫_ℝ=overlap x y := by
  change (∑ i : Fin n,(spin (y i)/Real.sqrt n)*(spin (x i)/Real.sqrt n))=overlap x y
  simp only [div_mul_div_comm,← sq,Real.sq_sqrt (Nat.cast_nonneg n),← Finset.sum_div]
  exact congrArg (fun z : ℝ => z/(n:ℝ)) (Finset.sum_congr rfl (fun i _ => mul_comm _ _))

@[simp] theorem overlap_flip_first {n : ℕ} (x y : Config n) : overlap (flip x) y = -overlap x y := by
  rw [overlap_comm,overlap_flip_right,overlap_comm x y]

theorem overlap_conflict_card {n : ℕ} (hn : 0<n) {I : Type*} [DecidableEq I]
    (S : Finset I) (v : I → Config n) (w : Config n) (b e : ℝ)
    (hb : 0<b) (he : 0≤e) (heb : e<b^2/2)
    (hpair : ∀ i∈S,∀ j∈S,i≠j → |overlap (v i) (v j)|≤e)
    (hlarge : ∀ i∈S,b< |overlap (v i) w|) : (S.card:ℝ)<2/b^2 := by
  let u (i : I) : Config n := if 0≤overlap (v i) w then v i else flip (v i)
  apply finite_unit_packing S (fun i => spinUnitVector (u i)) (spinUnitVector w) b e hb he heb
  · rw [spinUnitVector_inner,overlap_self hn]
  · intro i hi; rw [spinUnitVector_inner,overlap_self hn]
  · intro i hi j hj hij
    rw [spinUnitVector_inner]
    have h := hpair i hi j hj hij
    dsimp only [u]
    split_ifs <;> (try simp only [overlap_flip_first,overlap_flip_right,neg_neg]) <;>
      linarith only [(abs_le.mp h).1,(abs_le.mp h).2]
  · intro i hi
    rw [spinUnitVector_inner]
    dsimp only [u]
    split_ifs with h
    · simpa only [abs_of_nonneg h] using hlarge i hi
    · simpa only [overlap_flip_first,abs_of_neg (lt_of_not_ge h)] using hlarge i hi

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ConflictSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem signed_locking_of_not_mem {n : ℕ} (v x y : Config n) (h b : ℝ)
    (hq : h≤overlap x y) (hx : |overlap v x|≤b) (hy : |overlap v y|≤b)
    (havoid : (![v,x,y] : ReplicaConfig n 3)∉signedLockingSet n h b) :
    |overlap v x-overlap v y|≤2*(n:ℝ)^(-(1:ℝ)/100) := by
  classical
  by_contra H
  apply havoid
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,hq,hx,hy,lt_of_not_ge H⟩

theorem magnitude_locking_of_signed_avoid {n : ℕ} (v x y : Config n) (h b : ℝ)
    (hq : h≤|overlap x y|) (hx : |overlap v x|≤b) (hy : |overlap v y|≤b)
    (havoid : (![v,x,y] : ReplicaConfig n 3)∉signedLockingSet n h b)
    (havoid' : (![v,x,flip y] : ReplicaConfig n 3)∉signedLockingSet n h b) :
    abs (|overlap v x|-|overlap v y|)≤2*(n:ℝ)^(-(1:ℝ)/100) := by
  by_cases hp : 0≤overlap x y
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans
      (signed_locking_of_not_mem v x y h b (by simpa only [abs_of_nonneg hp] using hq) hx hy havoid)
  · have H := signed_locking_of_not_mem v x (flip y) h b
      (by simpa only [overlap_flip_right,abs_of_neg (lt_of_not_ge hp)] using hq)
      hx (by simpa only [overlap_flip_right,abs_neg] using hy) havoid'
    simpa only [overlap_flip_right,abs_neg] using (abs_abs_sub_abs_le_abs_sub _ _).trans H

theorem conflicts_are_suffix {n : ℕ} (A : Finset ℕ) (v : ℕ → Config n) (w : Config n)
    (r : ℕ → ℝ) (b b' t E F ρ : ℝ)
    (_hE : 0≤E) (ht : 0≤t) (hsmall : 2*t+E+F<b')
    (hsep : 2*E+2*F<3*ρ)
    (hr : ∀ i∈A,r i∈Icc t (2*t))
    (hspacing : ∀ i∈A,∀ j∈A,i<j → 3*ρ ≤ r j-r i)
    (hold : ∀ i∈A,∀ j∈A,i<j → |overlap (v i) (v j)-r i|≤E)
    (htransfer : ∀ i∈A,|overlap (v i) w|≤b → |overlap (v i) w-r i|≤E+F)
    (hlock : ∀ i∈A,∀ j∈A,i<j → b< |overlap (v i) w| →
      |overlap (v j) (v i)|≤b' → |overlap (v j) w|≤b' →
      abs (|overlap (v j) (v i)|-|overlap (v j) w|)≤F)
    (hF : 0≤F) :
    IsRetainedSuffix A (A.filter (fun i => b< |overlap (v i) w|)) := by
  classical
  constructor
  · exact Finset.filter_subset _ _
  · intro i j hi hj hij
    have hi' := (Finset.mem_filter.mp hi).1
    have hb := (Finset.mem_filter.mp hi).2
    by_cases hij' : i=j
    · simpa [hij'] using hi
    · have hijlt : i<j := lt_of_le_of_ne hij hij'
      by_contra h
      have hjc : |overlap (v j) w|≤b := by
        simpa only [Finset.mem_filter,hj,true_and,not_lt] using h
      have HO := hold i hi' j hj hijlt
      rw [overlap_comm (v i) (v j)] at HO
      have HN := htransfer j hj hjc
      have hri : 0 ≤ r i := ht.trans (hr i hi').1
      have hrj : 0 ≤ r j := ht.trans (hr j hj).1
      have HOA : abs (|overlap (v j) (v i)|-r i)≤E := by
        simpa only [abs_of_nonneg hri] using (abs_abs_sub_abs_le_abs_sub _ _).trans HO
      have HNA : abs (|overlap (v j) w|-r j)≤E+F := by
        simpa only [abs_of_nonneg hrj] using (abs_abs_sub_abs_le_abs_sub _ _).trans HN
      have hbi : |overlap (v j) (v i)|≤b' := by
        linarith only [(abs_le.mp HOA).2,(hr i hi').2,hsmall,hF]
      have hbj : |overlap (v j) w|≤b' := by
        linarith only [(abs_le.mp HNA).2,(hr j hj).2,hsmall]
      have HL := hlock i hi' j hj hijlt hb hbi hbj
      linarith only [(abs_le.mp HOA).2,(abs_le.mp HNA).1,(abs_le.mp HL).1,
        hspacing i hi' j hj hijlt,hsep]

theorem conflict_filter_card {n : ℕ} (hn : 0<n) (A : Finset ℕ)
    (v : ℕ → Config n) (w : Config n) (b e : ℝ)
    (hb : 0<b) (he : 0≤e) (heb : e<b^2/2)
    (hpair : ∀ i∈A,∀ j∈A,i≠j → |overlap (v i) (v j)|≤e) :
    (A.filter (fun i => b< |overlap (v i) w|)).card≤⌈2/b^2⌉₊ := by
  classical
  have H := overlap_conflict_card hn (A.filter (fun i => b< |overlap (v i) w|)) v w b e hb he heb
    (fun i hi j hj hij => hpair i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  exact_mod_cast H.le.trans (Nat.le_ceil (2/b^2))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ProtectedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem protected_block_step (B H j : ℕ) (hB : 0 < B) (hHB : H < B)
    (A D : Finset ℕ) (hA : ∀ i ∈ A, i < j) (hc : BlockProtected B j A)
    (hs : IsRetainedSuffix A D) (hcard : D.card ≤ H)
    (hcompat : j%B ≠ 0 → j-1∉D) :
    BlockProtected B (j+1) (insert j (A\D)) ∧ (0 < j → 0 ∈ A\D) := by
  classical
  obtain ⟨hc,hm⟩ := hc
  have hdecomp : j%B+j/B*B=j := by simpa only [Nat.mul_comm B] using Nat.mod_add_div j B
  have hprevle := Nat.div_mul_le_self (j-1) B
  by_cases hr : j%B=0
  · have hjmul : j/B*B=j := by omega
    have hsurvive (i : ℕ) (hi : i ∈ A) (hij : i ≤ j-B) : i ∈ A\D := by
      have hj0 : 0 < j := by have := hA i hi; omega
      have hBj : B ≤ j := Nat.le_of_dvd hj0 (Nat.dvd_of_mod_eq_zero hr)
      have hq : j/B=(j-1)/B+1 := by
        simpa only [Nat.sub_add_cancel hj0] using
          (Nat.succ_div_of_dvd (a:=j-1) (b:=B) (by simpa only [Nat.sub_add_cancel hj0] using Nat.dvd_of_mod_eq_zero hr))
      have ht : (j-1)/B*B=j-B := by
        have hx := congrArg (fun z : ℕ => z*B) hq
        simp only [Nat.add_mul,one_mul] at hx
        omega
      have hb : Finset.Ico (j-B) (j-B+B) ⊆ A := by
        intro k hk
        have hkj := Finset.mem_Ico.mp hk
        exact hc k (by omega) (by omega)
      exact retainedSuffix_preserves_before_block hs hcard hHB hb hi hij
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i hil hij
      simp only [Nat.add_sub_cancel] at hil
      have : i=j := by omega
      subst i
      exact Finset.mem_insert_self _ _
    · intro k hk
      by_cases he : k*B=j
      · rw [he]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply hsurvive _ (hm k (by omega))
        have hlt : k < j/B := (Nat.mul_lt_mul_right hB).mp (by omega)
        have hx := Nat.mul_le_mul_right B (show k+1 ≤ j/B by omega)
        simp only [Nat.add_mul,one_mul] at hx
        omega
    · intro hj
      apply hsurvive 0
      · simpa using hm 0 (by simpa using hj)
      · omega
  · have hj0 : 0 < j := by
      by_contra h
      have hjz : j=0 := by omega
      subst j
      exact hr (by simp)
    have hq : j/B=(j-1)/B := by
      simpa only [Nat.sub_add_cancel hj0] using
        (Nat.succ_div_of_not_dvd (a:=j-1) (b:=B) (by
          simpa only [Nat.sub_add_cancel hj0] using (fun h => hr (Nat.mod_eq_zero_of_dvd h))))
    have hqmul := congrArg (fun z : ℕ => z*B) hq
    have hjlast : j-1 ∈ A := hc (j-1) (by omega) (by omega)
    have hD0 := retainedSuffix_empty_of_last hs (fun i hi => by have := hA i hi; omega) hjlast (hcompat hr)
    rw [hD0,Finset.sdiff_empty]
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i hil hij
      simp only [Nat.add_sub_cancel] at hil
      by_cases he : i=j
      · rw [he]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hc i (by omega) (by omega))
    · intro k hk
      by_cases he : k*B=j
      · rw [he]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hm k (by omega))
    · intro _
      simpa using hm 0 (by simpa using hj0)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GreedyStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem greedy_locking_step {n : ℕ} (hn : 0 < n) (μ : ProbabilityMeasure ℝ)
    (v : ℕ → Config n) (w : Config n) (x : ℕ → Config n) (A : Finset ℕ)
    (r : ℕ → ℝ) (B H j u : ℕ) (t ρ E d b b' q : ℝ)
    (hj : 0 < j) (hB : 0 < B) (hHB : H < B) (hH : ⌈2/b^2⌉₊ ≤ H)
    (ht : 0 < t) (hρ : 0 < ρ) (hE : 0 ≤ E) (hd : 0 ≤ d) (hb : 0 < b)
    (hpack : 3*t < b^2/2) (hcsmall : 3*t < b) (hEst : E < t)
    (hsmall' : 2*t+E+2*(n:ℝ)^(-(1:ℝ)/100) < b')
    (hsep' : 2*E+4*(n:ℝ)^(-(1:ℝ)/100) < 3*ρ)
    (hwidth : ρ^8 < t/2)
    (hsmall : E+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+d/2 < ρ^8)
    (hsep : E+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+3*d/2 ≤ 2*ρ)
    (hd' : d/2 ≤ ρ^20) (heta : 2*(n:ℝ)^(-(1:ℝ)/100) < 2*ρ^20)
    (hq : 2*t+E+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20 < q)
    (hr : ∀ i ≤ j, r i ∈ Icc t (2*t))
    (hspacing : ∀ i k, i < k → k ≤ j → 3*ρ ≤ r k-r i)
    (hmass : ∀ i < j, (μ : Measure ℝ).real (Icc (r i-2*ρ^8) (r i+2*ρ^8)) ≤ ρ^4)
    (hA : ∀ i ∈ A, i < j) (hblock : BlockProtected B j A)
    (hpath : ∀ i ∈ A, |overlap (v i) (x u)-r i| ≤ E)
    (hpair : ∀ i ∈ A, ∀ k ∈ A, i < k → |overlap (v i) (v k)-r i| ≤ E)
    (hanchor : q ≤ overlap (v 0) (x 0)) (htarget : q ≤ overlap w (x u))
    (hcell : j%B ≠ 0 → |overlap (v (j-1)) w| ≤ 3*t)
    (hjump : ∀ z k, k < u → |overlap z (x (k+1))-overlap z (x k)| ≤ d)
    (hsigned : ∀ i ∈ A, (![v i,w,x u] : ReplicaConfig n 3) ∉ signedLockingSet n q b)
    (hbank : ∀ i ∈ A, ∀ k ∈ A, i < k →
      (![v k,v i,w] : ReplicaConfig n 3) ∉ signedLockingSet n b b' ∧
      (![v k,v i,flip w] : ReplicaConfig n 3) ∉ signedLockingSet n b b')
    (hnarrow : ∀ i ∈ A, ∀ k ≤ u,
      (![v i,x k,w] : ReplicaConfig n 3) ∉ narrowLockingSet n μ t ρ) :
    let D := A.filter (fun i => b < |overlap (v i) w|)
    let C := A\D
    let τ := lastCrossing (fun k => overlap w (x k)) (r j) u
    IsRetainedSuffix A D ∧ D.card ≤ H ∧ BlockProtected B (j+1) (insert j C) ∧
      0 ∈ C ∧ τ ≤ u ∧ overlap w (x τ) ∈ Icc (r j-d) (r j) ∧
      (∀ i ∈ C, |overlap (v i) w-r i| ≤ E+2*(n:ℝ)^(-(1:ℝ)/100)) ∧
      (∀ i ∈ C, |overlap (v i) (x τ)-r i| ≤ E+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20) := by
  classical
  let F := 2*(n:ℝ)^(-(1:ℝ)/100)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let D := A.filter (fun i => b < |overlap (v i) w|)
  let C := A\D
  have hc (i : ℕ) (hi : i ∈ C) : i ∈ A ∧ |overlap (v i) w| ≤ b := by
    have H := Finset.mem_sdiff.mp hi
    exact ⟨H.1,le_of_not_gt (fun hh => H.2 (Finset.mem_filter.mpr ⟨H.1,hh⟩))⟩
  have htransfer (i : ℕ) (hi : i ∈ A) (hcomp : |overlap (v i) w| ≤ b) :
      |overlap (v i) w-overlap (v i) (x u)| ≤ F := by
    apply signed_locking_of_not_mem (v i) w (x u) q b htarget hcomp _ (hsigned i hi)
    have hh := abs_add_le (overlap (v i) (x u)-r i) (r i)
    have hri := hr i (hA i hi).le
    rw [sub_add_cancel,abs_of_pos (ht.trans_le hri.1)] at hh
    linarith only [hh,hpath i hi,hri.2,hEst,hcsmall]
  have href (i : ℕ) (hi : i ∈ A) (hcomp : |overlap (v i) w| ≤ b) :
      |overlap (v i) w-r i| ≤ E+F := by
    have hh := abs_add_le (overlap (v i) w-overlap (v i) (x u)) (overlap (v i) (x u)-r i)
    rw [sub_add_sub_cancel] at hh
    linarith only [hh,htransfer i hi hcomp,hpath i hi]
  have hs : IsRetainedSuffix A D := by
    apply conflicts_are_suffix A v w r b b' t E F ρ hE ht.le hsmall' (by dsimp [F]; linarith only [hsep'])
      (fun i hi => hr i (hA i hi).le) (fun i hi k hk hik => hspacing i k hik (hA k hk).le) hpair href _ hF
    intro i hi k hk hik hconf hki hkw
    exact magnitude_locking_of_signed_avoid (v k) (v i) w b b' hconf.le hki hkw
      (hbank i hi k hk hik).1 (hbank i hi k hk hik).2
  have hcard : D.card ≤ H := by
    apply (conflict_filter_card hn A v w b (3*t) hb (by positivity) hpack _).trans hH
    intro i hi k hk hik
    have HH : |overlap (v i) (v k)-r (min i k)| ≤ E := by
      rcases lt_or_gt_of_ne hik with h | h
      · simpa only [min_eq_left h.le] using hpair i hi k hk h
      · simpa only [min_eq_right h.le,overlap_comm (v k) (v i)] using hpair k hk i hi h
    have hm : min i k ≤ j := (min_le_left _ _).trans (hA i hi).le
    have hh := abs_add_le (overlap (v i) (v k)-r (min i k)) (r (min i k))
    rw [sub_add_cancel,abs_of_pos (ht.trans_le (hr _ hm).1)] at hh
    linarith only [hh,HH,(hr _ hm).2,hEst]
  have hp := protected_block_step B H j hB hHB A D hA hblock hs hcard (by
    intro hmod hmem
    have hh := (Finset.mem_filter.mp hmem).2
    linarith only [hh,hcell hmod,hcsmall])
  have hzero : 0 ∈ C := hp.2 hj
  have hqj : r j < overlap w (x u) := by
    have hpow : 0 ≤ ρ^20 := by positivity
    dsimp [F] at hF
    linarith only [(hr j le_rfl).2,htarget,hq,hE,hF,hpow]
  have hsend (i : ℕ) (hi : i ∈ C) : |overlap (v i) (x u)-overlap (v i) w| < 2*ρ^20 := by
    rw [abs_sub_comm]
    exact (htransfer i (hc i hi).1 (hc i hi).2).trans_lt heta
  have hex := anchored_backwards_crossing μ (v 0) w x t ρ (E+F) d (r 0) (r j) q u
    ht hρ (hr 0 (by omega)) (hspacing 0 j hj le_rfl) hwidth hsmall hsep hd hd'
    (by dsimp [F]; linarith only [(hr 0 (by omega)).2,hq]) (hmass 0 hj)
    (href 0 (hc 0 hzero).1 (hc 0 hzero).2) hanchor hqj (hsend 0 hzero) hjump
    (hnarrow 0 (hc 0 hzero).1)
  have hlu := lastCrossing_le (fun k => overlap w (x k)) (r j) u
  refine ⟨hs,hcard,hp.1,hzero,hlu,lastCrossing_band _ _ _ _ hqj hex (hjump w),?_,?_⟩
  · intro i hi
    exact href i (hc i hi).1 (hc i hi).2
  · intro i hi
    have hiA := (hc i hi).1
    have Hn := narrow_backwards_transfer μ (v i) w x t ρ (E+F) d (r i) (r j) hlu
      ht hρ (hr i (hA i hiA).le) (hspacing i j (hA i hiA) le_rfl) hwidth hsmall hsep hd'
      (hmass i (hA i hiA)) (href i hiA (hc i hi).2) (hsend i hi)
      (fun k _ hk => hjump (v i) k hk)
      (lastCrossing_search _ _ _ _ hd hqj (hjump w))
      (fun k _ hk => hnarrow i hiA k hk) _ le_rfl hlu
    have HH := abs_add_le (overlap (v i) (x (lastCrossing (fun k => overlap w (x k)) (r j) u))-overlap (v i) w)
      (overlap (v i) w-r i)
    rw [sub_add_sub_cancel] at HH
    have HH2 := href i hiA (hc i hi).2
    dsimp [F] at HH2
    linarith only [HH,Hn,HH2]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GreedyInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem greedy_marker_windows {n : ℕ} (hn : 0 < n) (μ : ProbabilityMeasure ℝ)
    (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (hf : ∀ j, fallback j ∈ pool j) (base : ℕ → Config n) (x : ℕ → Config n)
    (r : ℕ → ℝ) (B H p m : ℕ) (t ρ d b b' q : ℝ)
    (hp : 0 < p) (hB : 0 < B) (hHB : H < B) (hH : ⌈2/b^2⌉₊ ≤ H)
    (ht : 0 < t) (hρ : 0 < ρ) (hd : 0 ≤ d) (hb : 0 < b)
    (hpack : 3*t < b^2/2) (hcsmall : 3*t < b) (hEst : 6*p*ρ^20 < t)
    (hsmall' : 2*t+6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100) < b')
    (hsep' : 12*p*ρ^20+4*(n:ℝ)^(-(1:ℝ)/100) < 3*ρ)
    (hwidth : ρ^8 < t/2)
    (hsmall : 6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+d/2 < ρ^8)
    (hsep : 6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+3*d/2 ≤ 2*ρ)
    (hd' : d/2 ≤ ρ^20) (heta : 2*(n:ℝ)^(-(1:ℝ)/100) < 2*ρ^20)
    (hq : 2*t+6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20 < q)
    (hr : ∀ i < p, r i ∈ Icc t (2*t))
    (hspacing : ∀ i j, i < j → j < p → 3*ρ ≤ r j-r i)
    (hmass : ∀ i < p, (μ : Measure ℝ).real (Icc (r i-2*ρ^8) (r i+2*ρ^8)) ≤ ρ^4)
    (hjump : ∀ z k, k < m → |overlap z (x (k+1))-overlap z (x k)| ≤ d)
    (hcoverage : ∀ j < p, ∀ v : ℕ → Config n, (∀ i < j, v i ∈ pool i) →
      ∀ u ≤ m, (∀ i, j/B*B ≤ i → i < j → |overlap (v i) (x u)| ≤ 3*t) →
      ∃ w ∈ pool j, q ≤ overlap w (x u) ∧
        ∀ i, j/B*B ≤ i → i < j → |overlap (v i) w| ≤ 3*t)
    (hsigned : ∀ i j, i < j → j < p → ∀ v ∈ pool i, ∀ w ∈ pool j, ∀ k ≤ m,
      (![v,w,x k] : ReplicaConfig n 3) ∉ signedLockingSet n q b)
    (hbank : ∀ i k j, i < k → k < j → j < p → ∀ v ∈ pool i, ∀ z ∈ pool k, ∀ w ∈ pool j,
      (![z,v,w] : ReplicaConfig n 3) ∉ signedLockingSet n b b' ∧
      (![z,v,flip w] : ReplicaConfig n 3) ∉ signedLockingSet n b b')
    (hnarrow : ∀ i j, i < j → j < p → ∀ v ∈ pool i, ∀ w ∈ pool j, ∀ k ≤ m,
      (![v,x k,w] : ReplicaConfig n 3) ∉ narrowLockingSet n μ t ρ)
    (hpass : overlap (bankPick pool fallback B x t q 0 base 0) (x m) ≤ 0) :
    ∃ k ≤ m, ∀ a, a*B < p →
      |overlap (greedyReference base (bankPick pool fallback B x t q) x r b m (a*B)) (x k)-r (a*B)| ≤ 6*p*ρ^20 := by
  classical
  let pick := bankPick pool fallback B x t q
  let S := greedyRun base pick x r b m
  have hε : 0 < ρ^20 := pow_pos hρ _
  have hη : 0 ≤ 2*(n:ℝ)^(-(1:ℝ)/100) := by positivity
  have htwo : 2*t < q := by
    have hEp : 0 ≤ 6*(p:ℝ)*ρ^20 := by positivity
    linarith only [hq,hEp,hε,hη]
  have hmem (j i : ℕ) (hi : i < j) : (S j).refs i ∈ pool i := by
    rw [show (S j).refs i=greedyReference base pick x r b m i from greedyRun_refs _ _ _ _ _ _ _ _ hi]
    exact bankPick_mem pool fallback hf B x t q i _ _
  have hfirst := bankPick_spec pool fallback B x t q 0 base 0
    (hcoverage 0 hp base (by intros; omega) 0 (by omega) (by intros; omega))
  have hanchor (j : ℕ) (hj : 0 < j) : q ≤ overlap ((S j).refs 0) (x 0) := by
    rw [show (S j).refs 0=greedyReference base pick x r b m 0 from greedyRun_refs _ _ _ _ _ _ _ _ hj]
    exact hfirst.1
  have HI : ∀ j ≤ p, (S j).time ≤ m ∧ BlockProtected B j (S j).kept ∧
      (∀ i ∈ (S j).kept, |overlap ((S j).refs i) (x (S j).time)-r i| ≤ 6*j*ρ^20) ∧
      (∀ i ∈ (S j).kept, ∀ k ∈ (S j).kept, i < k →
        |overlap ((S j).refs i) ((S j).refs k)-r i| ≤ 6*j*ρ^20) := by
    intro j hjp
    induction j with
    | zero => simp [S,greedyRun,BlockProtected]
    | succ j ih =>
      have hjp' : j < p := by omega
      obtain ⟨hτ,hblock,hpath,hpair⟩ := ih (by omega)
      have hEr : 6*(j:ℝ)*ρ^20 ≤ 6*p*ρ^20 := by gcongr
      have hA := greedyRun_range base pick x r b m j
      have hcand := hcoverage j hjp' (S j).refs (hmem j) (S j).time hτ (by
        intro i hil hij
        have hlo : (j-1)/B*B ≤ j/B*B := Nat.mul_le_mul_right B (Nat.div_le_div_right (Nat.sub_le j 1))
        have himem := hblock.1 i (hlo.trans hil) hij
        have hh := hpath i himem
        have hri := hr i (hij.trans hjp')
        have hh' := abs_add_le (overlap ((S j).refs i) (x (S j).time)-r i) (r i)
        rw [sub_add_cancel,abs_of_pos (ht.trans_le hri.1)] at hh'
        linarith only [hh',hh,hri.2,hEr,hEst])
      have hsel := bankPick_spec pool fallback B x t q j (S j).refs (S j).time hcand
      let w := pick j (S j).refs (S j).time
      have hw : w ∈ pool j := bankPick_mem pool fallback hf B x t q j _ _
      by_cases hj0 : j=0
      · subst j
        have hband := firstCrossing_band (fun k => overlap w (x k)) (r 0) d m
          (by change r 0 < overlap (bankPick pool fallback B x t q 0 base 0) (x 0); linarith only [hfirst.1,(hr 0 hp).2,htwo])
          (by change overlap (bankPick pool fallback B x t q 0 base 0) (x m) ≤ r 0; linarith only [hpass,(hr 0 hp).1,ht])
          (hjump w)
        dsimp [w, S, greedyRun] at hband
        change _ ≤ m ∧ _ ∧ _ ∧ _
        simp only [S,greedyRun,zero_add,Nat.cast_one,mul_one]
        simp only [Finset.empty_sdiff,Finset.insert_empty,Finset.mem_singleton,ite_true]
        refine ⟨hband.1,?_,?_,?_⟩
        · constructor
          · intro i _ hi
            have : i=0 := by omega
            simpa only [Finset.mem_singleton] using this
          · intro k hk
            have : k*B=0 := by omega
            simpa only [Finset.mem_singleton] using this
        · intro i hi
          subst i
          simp only [Function.update_self]
          rw [abs_le]
          constructor <;> linarith only [hband.2.1,hband.2.2,hd',hε]
        · intro i hi k hk hik
          omega
      · have hj : 0 < j := Nat.pos_of_ne_zero hj0
        have Hstep := greedy_locking_step hn μ (S j).refs w x (S j).kept r B H j (S j).time
          t ρ (6*j*ρ^20) d b b' q hj hB hHB hH ht hρ (by positivity) hd hb hpack hcsmall
          (hEr.trans_lt hEst) (by linarith only [hsmall',hEr]) (by linarith only [hsep',hEr]) hwidth
          (by linarith only [hsmall,hEr]) (by linarith only [hsep,hEr]) hd' heta
          (by linarith only [hq,hEr]) (fun i hi => hr i (hi.trans_lt hjp'))
          (fun i k hik hk => hspacing i k hik (hk.trans_lt hjp')) (fun i hi => hmass i (hi.trans hjp'))
          hA hblock hpath hpair (hanchor j hj) hsel.1
          (by
            intro hmod
            apply hsel.2 (j-1) _ (by omega)
            have hh : j%B+j/B*B=j := by simpa only [Nat.mul_comm B] using Nat.mod_add_div j B
            have hpos : 0 < j%B := Nat.pos_of_ne_zero hmod
            omega)
          (fun z k hk => hjump z k (hk.trans_le hτ))
          (fun i hi => hsigned i j (hA i hi) hjp' _ (hmem j i (hA i hi)) w hw _ hτ)
          (fun i hi k hk hik => hbank i k j hik (hA k hk) hjp' _ (hmem j i (hA i hi)) _ (hmem j k (hA k hk)) w hw)
          (fun i hi k hk => hnarrow i j (hA i hi) hjp' _ (hmem j i (hA i hi)) w hw k (hk.trans hτ))
        obtain ⟨hs,hcard,hprot,hzero,htime,hband,href,hnewpath⟩ := Hstep
        have hinc : 6*(j:ℝ)*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20 ≤ 6*(j+1:ℕ)*ρ^20 := by
          simp only [Nat.cast_add,Nat.cast_one]
          nlinarith only [heta,hε]
        have hmono : 6*(j:ℝ)*ρ^20 ≤ 6*(j+1:ℕ)*ρ^20 := by
          simp only [Nat.cast_add,Nat.cast_one]; nlinarith only [hε]
        change _ ≤ m ∧ _ ∧ _ ∧ _
        simp only [S,greedyRun,ite_eq_right hj0]
        refine ⟨htime.trans hτ,hprot,?_,?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with he | hi
          · subst i
            rw [Function.update_self,abs_le]
            have hc : 2*ρ^20 ≤ 6*(j+1:ℕ)*ρ^20 := by
              have hjr : (0:ℝ) ≤ j := by positivity
              simp only [Nat.cast_add,Nat.cast_one]; nlinarith only [mul_nonneg hjr hε.le,hε]
            constructor <;> linarith only [hband.1,hband.2,hd',hc]
          · have him : i ∈ (S j).kept := (Finset.mem_sdiff.mp hi).1
            rw [Function.update_of_ne (ne_of_lt (hA i him))]
            exact (hnewpath i hi).trans hinc
        · intro i hi k hk hik
          have hil : i < j := by
            rcases Finset.mem_insert.mp hk with rfl | hk
            · exact hik
            · exact hik.trans (hA k (Finset.mem_sdiff.mp hk).1)
          have him : i ∈ (S j).kept\(S j).kept.filter (fun i => b < |overlap ((S j).refs i) w|) := by
            exact (Finset.mem_insert.mp hi).resolve_left (ne_of_lt hil)
          rw [Function.update_of_ne (ne_of_lt hil)]
          rcases Finset.mem_insert.mp hk with rfl | hk
          · rw [Function.update_self]
            exact (href i him).trans (by linarith only [hinc,hε])
          · have hkl := hA k (Finset.mem_sdiff.mp hk).1
            rw [Function.update_of_ne (ne_of_lt hkl)]
            exact (hpair i (Finset.mem_sdiff.mp him).1 k (Finset.mem_sdiff.mp hk).1 hik).trans hmono
  obtain ⟨hτ,hprotected,hpath,_⟩ := HI p le_rfl
  refine ⟨(S p).time,hτ,?_⟩
  intro a ha
  have hmem := hprotected.2 a ha
  rw [← greedyRun_refs base pick x r b m p (a*B) ha]
  exact hpath (a*B) hmem

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GridThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

namespace FiniteLaw

theorem uniformFin_prob (n : ℕ) (hn : 0 < n) (E : Fin n → Prop) :
    (uniformFin n hn).prob E=(Finset.univ.filter E).card/(n:ℝ) := by
  simp only [prob,expect,uniformFin,← Finset.mul_sum]
  rw [Finset.sum_boole]
  ring

theorem markov {n : ℕ} (P : FiniteLaw (Fin n)) (f : Fin n → ℝ) (hf : ∀ x, 0 ≤ f x)
    (c : ℝ) (_hc : 0 < c) : c*P.prob (fun x => c < f x) ≤ P.expect f := by
  rw [prob,← expect_const_mul]
  apply expect_mono
  intro x
  split_ifs with h
  · simpa only [mul_one] using h.le
  · simpa only [mul_zero] using hf x
end FiniteLaw

theorem thresholdGrid_mem {n : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ)
    (a : ℝ) (i : Fin n) : thresholdGrid n a ρ i ∈ Icc a (a+ρ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hi : (i:ℝ)<n := by exact_mod_cast i.isLt
  unfold thresholdGrid
  constructor
  · have : 0 ≤ ρ*(i:ℕ)/(n:ℝ) := by positivity
    linarith only [this]
  · have : ρ*(i:ℕ)/(n:ℝ) ≤ ρ := (div_le_iff₀ hnR).mpr (by gcongr)
    linarith only [this]

theorem thresholdGrid_count {n : ℕ} (hn : 0 < n) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 ≤ w)
    (a x : ℝ) :
    ((Finset.univ.filter (fun i : Fin n => |thresholdGrid n a ρ i-x| ≤ w)).card:ℝ) ≤
      2*w*(n:ℝ)/ρ+1 := by
  let S := Finset.univ.filter (fun i : Fin n => |thresholdGrid n a ρ i-x| ≤ w)
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  by_cases hs : S.Nonempty
  · let i := S.min' hs
    let j := S.max' hs
    have hi : i∈S := Finset.min'_mem S hs
    have hj : j∈S := Finset.max'_mem S hs
    have hij : i≤j := Finset.min'_le S j hj
    have hcard : S.card ≤ (j:ℕ)+1-(i:ℕ) := by
      rw [← Fin.card_Icc]
      apply Finset.card_le_card
      intro z hz
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S z hz,Finset.le_max' S z hz⟩
    have hcard' : (S.card:ℝ) ≤ (j:ℝ)-(i:ℝ)+1 := by
      have hnat : (i:ℕ)≤(j:ℕ)+1 := by omega
      have hc : (S.card:ℝ) ≤ (((j:ℕ)+1-(i:ℕ):ℕ):ℝ) := by exact_mod_cast hcard
      rw [Nat.cast_sub hnat,Nat.cast_add,Nat.cast_one] at hc
      linarith only [hc]
    have hdi := abs_le.mp ((Finset.mem_filter.mp hi).2)
    have hdj := abs_le.mp ((Finset.mem_filter.mp hj).2)
    have hgap : ρ*((j:ℝ)-(i:ℝ)) ≤ 2*w*(n:ℝ) := by
      have H : thresholdGrid n a ρ j-thresholdGrid n a ρ i ≤ 2*w := by linarith only [hdi.1,hdj.2]
      have HH : thresholdGrid n a ρ j-thresholdGrid n a ρ i=ρ*((j:ℝ)-(i:ℝ))/(n:ℝ) := by
        unfold thresholdGrid
        ring
      rw [HH,div_le_iff₀ hnR] at H
      exact H
    have hgap' : (j:ℝ)-(i:ℝ) ≤ 2*w*(n:ℝ)/ρ := (le_div_iff₀ hρ).mpr (by nlinarith only [hgap])
    exact hcard'.trans (by linarith only [hgap'])
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (S.card:ℝ)≤_
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem thresholdGrid_window {n : ℕ} (hn : 0 < n) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 ≤ w)
    (a x : ℝ) :
    (FiniteLaw.uniformFin n hn).prob (fun i => |thresholdGrid n a ρ i-x| ≤ w) ≤ 2*w/ρ+1/(n:ℝ) := by
  rw [FiniteLaw.uniformFin_prob]
  have h := div_le_div_of_nonneg_right (thresholdGrid_count hn hρ hw a x) (by positivity : (0:ℝ)≤n)
  refine h.trans_eq ?_
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

theorem thresholdGrid_mass_expect {n : ℕ} (hn : 0 < n) (μ : ProbabilityMeasure ℝ)
    {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 ≤ h) (a : ℝ) :
    (FiniteLaw.uniformFin n hn).expect (fun i => (μ:Measure ℝ).real
      (Icc (thresholdGrid n a ρ i-h) (thresholdGrid n a ρ i+h))) ≤ 2*h/ρ+1/(n:ℝ) := by
  let f (i : Fin n) := (Icc (thresholdGrid n a ρ i-h) (thresholdGrid n a ρ i+h)).indicator (fun _ : ℝ => (1:ℝ))
  have hi (i : Fin n) : Integrable (f i) (μ:Measure ℝ) :=
    (integrable_const 1).indicator measurableSet_Icc
  have he : (FiniteLaw.uniformFin n hn).expect (fun i => (μ:Measure ℝ).real
      (Icc (thresholdGrid n a ρ i-h) (thresholdGrid n a ρ i+h))) =
      ∫ x, (1/(n:ℝ))*∑ i, f i x ∂(μ:Measure ℝ) := by
    unfold FiniteLaw.expect FiniteLaw.uniformFin
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [integral_indicator_const (1:ℝ) measurableSet_Icc]
    simp only [smul_eq_mul,mul_one]
  rw [he]
  have hb (x : ℝ) : (1/(n:ℝ))*∑ i, f i x ≤ 2*h/ρ+1/(n:ℝ) := by
    have H := thresholdGrid_window hn hρ hh a x
    change (1/(n:ℝ))*(∑ i, f i x)≤_
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    unfold FiniteLaw.prob FiniteLaw.expect FiniteLaw.uniformFin
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have he : x∈Icc (thresholdGrid n a ρ i-h) (thresholdGrid n a ρ i+h) ↔ |thresholdGrid n a ρ i-x|≤h := by
      rw [Set.mem_Icc,abs_le]
      constructor <;> intro H <;> constructor <;> linarith only [H.1,H.2]
    simp only [f,Set.indicator_apply,he]
  exact (integral_mono_of_nonneg (ae_of_all _ (fun x => by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)))
    (integrable_const _) (ae_of_all _ hb)).trans_eq (by simp)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_PredictableGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

theorem gridThresholds_prefix (n p j : ℕ) (t ρ : ℝ) (z : Fin p → Fin n) (hj : j<p) :
    ∀ i<j, gridThresholds n p t ρ z i =
      gridThresholds n j t ρ (fun a => z ⟨a.val,a.isLt.trans hj⟩) i := by
  intro i hij
  simp only [gridThresholds,dite_eq_left hij,dite_eq_left (hij.trans hj)]

theorem gridThresholds_good_mass {n : ℕ} (hn : 0<n) (μ : ProbabilityMeasure ℝ)
    (p : ℕ) (t ρ : ℝ) (hρ : 0<ρ) :
    ((FiniteLaw.uniformFin n hn).iid (Fin p)).prob (fun z => ∃ i : Fin p,
      ρ^4 < (μ:Measure ℝ).real (Icc (thresholdGrid n (t+4*i.val*ρ) ρ (z i)-2*ρ^8)
        (thresholdGrid n (t+4*i.val*ρ) ρ (z i)+2*ρ^8))) ≤
      p*((4*ρ^8/ρ+1/(n:ℝ))/ρ^4) := by
  classical
  let P := FiniteLaw.uniformFin n hn
  refine (FiniteLaw.prob_exists _ _).trans ?_
  calc
    _ ≤ ∑ i : Fin p, (4*ρ^8/ρ+1/(n:ℝ))/ρ^4 := by
      apply Finset.sum_le_sum
      intro i _
      rw [P.iid_prob_single i (fun u => ρ^4 < (μ:Measure ℝ).real
        (Icc (thresholdGrid n (t+4*i.val*ρ) ρ u-2*ρ^8) (thresholdGrid n (t+4*i.val*ρ) ρ u+2*ρ^8)))]
      have HM := P.markov (fun u => (μ:Measure ℝ).real
          (Icc (thresholdGrid n (t+4*i.val*ρ) ρ u-2*ρ^8) (thresholdGrid n (t+4*i.val*ρ) ρ u+2*ρ^8)))
        (fun _ => measureReal_nonneg) (ρ^4) (pow_pos hρ _)
      have HE := thresholdGrid_mass_expect hn μ hρ (by positivity : 0≤2*ρ^8) (t+4*i.val*ρ)
      apply (le_div_iff₀ (pow_pos hρ 4)).mpr
      have HR : 2*(2*ρ^8)/ρ=4*ρ^8/ρ := by ring
      rw [HR] at HE
      simpa only [mul_comm] using HM.trans HE
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem prod_block_marker (B s : ℕ) (hB : 0<B) (γ : ℝ) :
    (∏ i : Fin (B*s), if i.val%B=0 then γ else 1)=γ^s := by
  classical
  let : NeZero B := ⟨hB.ne'⟩
  have hfirst : (∏ i : Fin B, if i.val%B=0 then γ else 1)=γ := by
    have he (i : Fin B) : i.val%B=0 ↔ i=0 := by rw [Nat.mod_eq_of_lt i.isLt]; exact (Fin.ext_iff (a := i) (b := (0:Fin B))).symm
    simp only [he]
    simp
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ,Fin.prod_univ_add]
    simp only [Fin.val_castAdd,Fin.val_natAdd]
    rw [show (∏ i : Fin B, if ((B*s)+i.val)%B=0 then γ else 1)=γ from by
      simpa only [Nat.add_mod,Nat.mul_mod_right,zero_add,Nat.mod_mod] using hfirst]
    rw [ih,pow_succ]

theorem greedy_grid_windows_bound {n : ℕ} (hn : 0<n) (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n) (x : ℕ → Config n)
    (B s m : ℕ) (hB : 0<B) (t ρ b w : ℝ) (hρ : 0<ρ) (hw : 0≤w) (k : ℕ) :
    ((FiniteLaw.uniformFin n hn).iid (Fin (B*s))).prob (fun z => ∀ i : Fin (B*s), i.val%B=0 →
      |overlap (greedyReference base pick x (gridThresholds n (B*s) t ρ z) b m i.val) (x k)-
        thresholdGrid n (t+4*i.val*ρ) ρ (z i)|≤w) ≤ (2*w/ρ+1/(n:ℝ))^s := by
  classical
  let P := FiniteLaw.uniformFin n hn
  let γ := 2*w/ρ+1/(n:ℝ)
  let E (j : ℕ) (z : Fin j → Fin n) (u : Fin n) := j%B=0 →
    |overlap (greedyReference base pick x (gridThresholds n j t ρ z) b m j) (x k)-
      thresholdGrid n (t+4*j*ρ) ρ u|≤w
  have hE (j : ℕ) (z : Fin j → Fin n) : P.prob (E j z) ≤ if j%B=0 then γ else 1 := by
    by_cases hj : j%B=0
    · rw [ite_eq_left hj]
      have H := thresholdGrid_window hn hρ hw (t+4*j*ρ)
        (overlap (greedyReference base pick x (gridThresholds n j t ρ z) b m j) (x k))
      simpa only [E,hj,true_implies,abs_sub_comm] using H
    · exact (P.prob_le_one _).trans_eq (ite_eq_right hj).symm
  have H := P.iid_predictable_bound E (fun j => if j%B=0 then γ else 1)
    (fun j => by dsimp only [γ]; split_ifs <;> positivity) hE (B*s)
  rw [prod_block_marker B s hB] at H
  refine (FiniteLaw.prob_mono _ (fun z hz i hi => ?_)).trans H
  have hr := gridThresholds_prefix n (B*s) i.val t ρ z i.isLt
  have he := greedyReference_predictable base pick x (gridThresholds n (B*s) t ρ z)
      (gridThresholds n i.val t ρ (fun a => z ⟨a.val,a.isLt.trans i.isLt⟩)) b m i.val hr
  rw [← he]
  exact hz i hi

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ThresholdObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

theorem gridThresholds_range {n p : ℕ} (hn : 0<n) {t ρ : ℝ} (hρ : 0<ρ)
    (hp : 4*p*ρ≤t) (z : Fin p → Fin n) : ∀i<p,gridThresholds n p t ρ z i∈Icc t (2*t) := by
  intro i hi
  rw [gridThresholds,dite_eq_left hi]
  have H := thresholdGrid_mem hn hρ (t+4*i*ρ) (z ⟨i,hi⟩)
  have hiR : (i:ℝ)+1≤p := by exact_mod_cast hi
  have h0 : 0≤4*(i:ℝ)*ρ := by positivity
  have h1 : 4*(i:ℝ)*ρ+ρ≤4*p*ρ := by nlinarith only [mul_nonneg (show 0≤(p:ℝ)-i-1 by linarith only [hiR]) hρ.le,hρ]
  constructor <;> linarith only [H.1,H.2,h0,h1,hp]

theorem gridThresholds_spacing {n p : ℕ} (hn : 0<n) {t ρ : ℝ} (hρ : 0<ρ)
    (z : Fin p → Fin n) : ∀i j,i<j → j<p → 3*ρ≤gridThresholds n p t ρ z j-gridThresholds n p t ρ z i := by
  intro i j hij hj
  rw [gridThresholds,dite_eq_left hj,gridThresholds,dite_eq_left (hij.trans hj)]
  have Hi := thresholdGrid_mem hn hρ (t+4*i*ρ) (z ⟨i,hij.trans hj⟩)
  have Hj := thresholdGrid_mem hn hρ (t+4*j*ρ) (z ⟨j,hj⟩)
  have hR : (i:ℝ)+1≤j := by exact_mod_cast hij
  have hM := mul_nonneg (show 0≤(j:ℝ)-i-1 by linarith only [hR]) hρ.le
  nlinarith only [Hi.2,Hj.1,hM]

theorem greedy_no_passage {n : ℕ} (hn : 0<n) (μ : ProbabilityMeasure ℝ)
    (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (hf : ∀j,fallback j∈pool j) (base : ℕ → Config n) (x : ℕ → Config n)
    (B H s m : ℕ) (t ρ d b b' q : ℝ) (G : GreedyScaleBounds n B H (B*s) t ρ d b b' q)
    (hcount : (B*s)*((4*ρ^8/ρ+1/(n:ℝ))/ρ^4)+(m+1)*(2*(6*(B*s)*ρ^20)/ρ+1/(n:ℝ))^s<1)
    (hjump : ∀ z k, k < m → |overlap z (x (k+1))-overlap z (x k)|≤d)
    (hcoverage : ∀ j < B*s,∀v : ℕ → Config n,(∀ i < j,v i∈pool i) →
      ∀ u ≤ m,(∀ i, j/B*B ≤ i → i<j → |overlap (v i) (x u)|≤3*t) →
      ∃w∈pool j,q≤overlap w (x u) ∧ ∀ i, j/B*B ≤ i → i<j → |overlap (v i) w|≤3*t)
    (hsigned : ∀i j,i<j → j<B*s → ∀v∈pool i,∀w∈pool j,∀ k ≤ m,
      (![v,w,x k] : ReplicaConfig n 3)∉signedLockingSet n q b)
    (hbank : ∀i k j,i<k → k<j → j<B*s → ∀v∈pool i,∀z∈pool k,∀w∈pool j,
      (![z,v,w] : ReplicaConfig n 3)∉signedLockingSet n b b' ∧
      (![z,v,flip w] : ReplicaConfig n 3)∉signedLockingSet n b b')
    (hnarrow : ∀i j,i<j → j<B*s → ∀v∈pool i,∀w∈pool j,∀ k ≤ m,
      (![v,x k,w] : ReplicaConfig n 3)∉narrowLockingSet n μ t ρ) :
    0<overlap (bankPick pool fallback B x t q 0 base 0) (x m) := by
  by_contra hpos
  have hpass : overlap (bankPick pool fallback B x t q 0 base 0) (x m)≤0 := le_of_not_gt hpos
  let p := B*s
  let P := (FiniteLaw.uniformFin n hn).iid (Fin p)
  let bad (z : Fin p → Fin n) := ∃i : Fin p,ρ^4 < (μ:Measure ℝ).real
    (Icc (thresholdGrid n (t+4*i.val*ρ) ρ (z i)-2*ρ^8) (thresholdGrid n (t+4*i.val*ρ) ρ (z i)+2*ρ^8))
  let W (k : Fin (m+1)) (z : Fin p → Fin n) := ∀i : Fin p,i.val%B=0 →
    |overlap (greedyReference base (bankPick pool fallback B x t q) x (gridThresholds n p t ρ z) b m i.val) (x k.val)-
      thresholdGrid n (t+4*i.val*ρ) ρ (z i)|≤6*p*ρ^20
  have hall : ∀z,bad z ∨ ∃k : Fin (m+1),W k z := by
    intro z
    by_cases hz : bad z
    · exact Or.inl hz
    · right
      have hm : ∀i<p,(μ:Measure ℝ).real (Icc (gridThresholds n p t ρ z i-2*ρ^8) (gridThresholds n p t ρ z i+2*ρ^8))≤ρ^4 := by
        intro i hi
        rw [gridThresholds,dite_eq_left hi]
        exact le_of_not_gt (fun H => hz ⟨⟨i,hi⟩,H⟩)
      obtain ⟨k,hk,Hk⟩ := greedy_marker_windows hn μ pool fallback hf base x (gridThresholds n p t ρ z)
        B H p m t ρ d b b' q G.p_pos G.B_pos G.HB G.packingH G.t_pos G.rho_pos G.d_nonneg G.b_pos
        G.packing G.cutoff G.total_error G.small_cutoff G.separation G.width G.small_width G.large_width
        G.jump G.eta G.high (gridThresholds_range hn G.rho_pos G.grid_range z)
        (gridThresholds_spacing hn G.rho_pos z) hm hjump hcoverage hsigned hbank hnarrow hpass
      refine ⟨⟨k,by omega⟩,?_⟩
      intro i hi
      have he : i.val/B*B=i.val := by
        have H := Nat.mod_add_div i.val B
        rw [hi,zero_add,Nat.mul_comm] at H
        exact H
      have H := Hk (i.val/B) (by simpa only [he] using i.isLt)
      rw [he,gridThresholds,dite_eq_left i.isLt] at H
      exact H
  have h1 : 1≤P.prob bad+P.prob (fun z => ∃k : Fin (m+1),W k z) := by
    have he : P.prob (fun z => bad z ∨ ∃k : Fin (m+1),W k z)=1 := by
      unfold FiniteLaw.prob
      simp only [hall,ite_true,FiniteLaw.expect_const]
    rw [← he]
    exact P.prob_or _ _
  have hm := gridThresholds_good_mass hn μ p t ρ G.rho_pos
  have hw : P.prob (fun z => ∃k : Fin (m+1),W k z)≤(m+1)*(2*(6*p*ρ^20)/ρ+1/(n:ℝ))^s := by
    refine (P.prob_exists W).trans ?_
    calc
      _ ≤ ∑ _k : Fin (m+1),(2*(6*p*ρ^20)/ρ+1/(n:ℝ))^s := by
        apply Finset.sum_le_sum
        intro k _
        exact greedy_grid_windows_bound hn base (bankPick pool fallback B x t q) x B s m G.B_pos t ρ b
          (6*p*ρ^20) G.rho_pos (by positivity) k.val
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  change P.prob bad≤_ at hm
  simp only [p,Nat.cast_mul] at hm hw h1
  linarith only [h1,hm,hw,hcount]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GreedyNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

 theorem greedyScale_of_slack {n B H s : ℕ} {t ρ b b' q : ℝ}
    (hn : 0<n) (hB : 0<B) (hH : H<B) (hs : 0 < s) (hpack : ⌈2/b^2⌉₊≤H)
    (ht : 0<t) (hb : 0<b) (hpack' : 3*t<b^2/2) (hcut : 3*t<b)
    (hρ : 0<ρ) (hρ1 : ρ<1)
    (hη : (n:ℝ)^(-(1:ℝ)/100)=ρ^100) (hInv : 1/(n:ℝ)=ρ^10000)
    (hp : (B*s:ℕ)*ρ≤t/8)
    (hF : greedySlack t ρ<ρ^8) (hFt : greedySlack t ρ<t)
    (hFb : 2*t+greedySlack t ρ<b') (hFq : 2*t+2*greedySlack t ρ<q)
    (hwidth : ρ^8<t/2) : GreedyScaleBounds n B H (B*s) t ρ (2/(n:ℝ)) b b' q := by
  have hρ8 : ρ^8≤ρ := pow_le_of_le_one hρ.le hρ1.le (by decide)
  have h20 : ρ^10000≤ρ^20 := pow_le_pow_of_le_one hρ.le hρ1.le (by decide)
  have h100 : ρ^100<ρ^20 := pow_lt_pow_right_of_lt_one₀ hρ hρ1 (by decide)
  have he : 6*(B*s:ℕ)*ρ^20≤(3*t/4)*ρ^19 := by
    have h := mul_le_mul_of_nonneg_right hp (show 0≤6*ρ^19 by positivity)
    nlinarith only [h]
  have hρ20 : 0≤ρ^20 := by positivity
  have hi : 0≤ρ^10000 := by positivity
  have hη0 : 0≤ρ^100 := by positivity
  have hd : 2/(n:ℝ)=2*ρ^10000 := by rw [← hInv]; ring
  have hp0 : 0≤6*(B*s:ℕ)*ρ^20 := by positivity
  have hF0 : 0≤greedySlack t ρ := by unfold greedySlack; positivity
  have heF : 6*(B*s:ℕ)*ρ^20+2*ρ^100+ρ^20+3*ρ^10000≤greedySlack t ρ := by
    unfold greedySlack; linarith only [he]
  constructor
  · exact Nat.mul_pos hB hs
  · exact hB
  · exact hH
  · exact hpack
  · exact ht
  · exact hρ
  · positivity
  · exact hb
  · exact hpack'
  · exact hcut
  · have := heF.trans_lt hFt; linarith only [this,hρ20,hi,hη0]
  · rw [hη]; linarith only [heF,hFb,hρ20,hi]
  · rw [hη]; nlinarith only [heF,hF,hρ8,hρ20,hi,hρ]
  · exact hwidth
  · rw [hη,hd]; linarith only [heF,hF,hi]
  · rw [hη,hd]; linarith only [heF,hF,hρ8,hρ]
  · rw [hd]; linarith only [h20]
  · rw [hη]; linarith only [h100]
  · rw [hη]; linarith only [heF,hFq,hi,hη0,hp0]
  · norm_num only [Nat.cast_mul] at hp ⊢; linarith only [hp,ht]

theorem levelRho_pos {n : ℕ} (hn : 0<n) : 0<levelRho n := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
theorem levelRho_tendsto : Tendsto levelRho atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num [kappa] : 0<kappa)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem levelRho_pow {n : ℕ} (hn : 0<n) (a : ℕ) : (levelRho n)^a=(n:ℝ)^(-((a:ℝ)*kappa)) := by
  unfold levelRho
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : (0:ℝ)≤n)]
  congr 1
  ring

theorem levelRho_inv {n : ℕ} (hn : 0<n) : 1/(n:ℝ)=(levelRho n)^10000 := by
  rw [levelRho_pow hn]
  norm_num [kappa,Real.rpow_neg_one]

theorem levelRho_eta {n : ℕ} (hn : 0<n) : (n:ℝ)^(-(1:ℝ)/100)=(levelRho n)^100 := by
  rw [levelRho_pow hn]; norm_num [kappa]

theorem levelLogScale_mul_rho {n : ℕ} (hn : 0<n) : levelLogScale n*levelRho n=1 := by
  unfold levelLogScale levelRho
  rw [← Real.rpow_add (by exact_mod_cast hn : (0:ℝ)<n)]
  simp

theorem greedyBlockCount_upper {n B : ℕ} (hn : 0<n) (hB : 0<B) {t : ℝ} (ht : 0<t) :
    (B*greedyBlockCount B t n:ℕ)*levelRho n≤t/8 := by
  have hB' : (0:ℝ)<B := by exact_mod_cast hB
  have h := Nat.floor_le (show 0≤(t/(8*B))*levelLogScale n by unfold levelLogScale; positivity)
  have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hB'.le) (levelRho_pos hn).le
  have he : (B:ℝ)*((t/(8*B))*levelLogScale n)*levelRho n=t/8 := by
    rw [mul_assoc (B:ℝ),mul_assoc,levelLogScale_mul_rho hn,mul_one]
    field_simp
  simpa only [greedyBlockCount,Nat.cast_mul,he] using h'

 theorem greedySlack_tendsto (t : ℝ) : Tendsto (fun n => greedySlack t (levelRho n)) atTop (𝓝 0) := by
  have H := (((levelRho_tendsto.pow 19).const_mul (3*t/4)).add ((levelRho_tendsto.pow 100).const_mul 2)).add
    (levelRho_tendsto.pow 20) |>.add ((levelRho_tendsto.pow 10000).const_mul 3)
  simpa only [greedySlack,zero_pow (by decide : 19≠0),zero_pow (by decide : 100≠0),zero_pow (by decide : 20≠0),zero_pow (by decide : 10000≠0),mul_zero,add_zero] using H

 theorem greedySlack_div_tendsto (t : ℝ) : Tendsto (fun n => greedySlack t (levelRho n)/(levelRho n)^8) atTop (𝓝 0) := by
  have H : Tendsto (fun n => (3*t/4)*(levelRho n)^11+2*(levelRho n)^92+(levelRho n)^12+3*(levelRho n)^9992) atTop (𝓝 0) := by
    convert (((levelRho_tendsto.pow 11).const_mul (3*t/4)).add ((levelRho_tendsto.pow 92).const_mul 2)).add
      (levelRho_tendsto.pow 12) |>.add ((levelRho_tendsto.pow 9992).const_mul 3) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hρ := (levelRho_pos hn).ne'
  unfold greedySlack
  field_simp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem gibbs_prob_eq_finiteMass {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (gibbsFiniteLaw β J).prob E=finiteMass (gibbs β J) (Finset.univ.filter E) := by
  unfold FiniteLaw.prob FiniteLaw.expect gibbsFiniteLaw finiteMass
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_filter]

 theorem gibbs_coverage_predicate {n : ℕ} (β : ℝ) (J : Disorder n) (q a δ : ℝ)
    (h : ∀ S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
      finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<a))<δ)
    (E : Config n → Prop) :
    (gibbsFiniteLaw β J).prob (fun x => E x ∧ (gibbsFiniteLaw β J).prob (fun y => E y ∧ q≤|overlap x y|)<a)≤δ := by
  have H := h (Finset.univ.filter E)
  simp_rw [Finset.filter_filter] at H
  refine le_trans ?_ H.le
  apply le_of_eq
  rw [gibbs_prob_eq_finiteMass]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,gibbs_prob_eq_finiteMass]
  apply and_congr_right
  intro _
  apply Iff.of_eq
  apply congrArg (fun r : ℝ => r<a)
  apply congrArg (finiteMass (gibbs β J))
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

 theorem coveragePrefix_nonneg (f : ℝ → ℝ) (hf : ∀x,0<f x) (j : ℕ) : 0 ≤ coveragePrefix f j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => simp only [coveragePrefix]; linarith only [ih,hf (coveragePrefix f j+5)]

 theorem bankPrefix_coverage (f : ℝ → ℝ) (j : ℕ) :
    bankPrefix (fun j => f (coveragePrefix f j+5)) j=coveragePrefix f j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [bankPrefix,coveragePrefix,ih]

 theorem exists_coverage_schedule (β q : ℝ)
    (h : ∀D : ℝ,0<D → ∃c : ℝ,0 < c ∧ ∃C : (n : ℕ) → Set (Disorder n),
      (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
      ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
        finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*levelLogScale n)))<Real.exp (-D*levelLogScale n)) :
    ∃c : ℕ → ℝ, (∀j,0 < c j) ∧ ∃C : ℕ → (n : ℕ) → Set (Disorder n),
      (∀j n,MeasurableSet (C j n)) ∧
      (∀j,Tendsto (fun n => (disorderLaw n).real (C j n)) atTop (𝓝 1)) ∧
      ∀j n J,J∈C j n → ∀E : Config n → Prop,
        (gibbsFiniteLaw β J).prob (fun x => E x ∧ (gibbsFiniteLaw β J).prob (fun y => E y ∧ q≤|overlap x y|)<Real.exp (-c j*levelLogScale n))≤
          Real.exp (-(bankPrefix c j+5)*levelLogScale n) := by
  choose f hf C hC hC1 hcov using (fun D : ℝ => h (max D 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
  let c : ℕ → ℝ := fun j => f (coveragePrefix f j+5)
  refine ⟨c,fun j => hf _,fun j => C (coveragePrefix f j+5),fun j n => hC _ n,fun j => hC1 _,?_⟩
  intro j n J hJ E
  have HD : max (coveragePrefix f j+5) 1=coveragePrefix f j+5 := max_eq_left (by linarith only [coveragePrefix_nonneg f hf j])
  have H := gibbs_coverage_predicate β J q _ _ (hcov (coveragePrefix f j+5) n J hJ) E
  simpa only [HD,c,bankPrefix_coverage] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_HighProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem high_probability_inter (C D : (n : ℕ) → Set (Disorder n))
    (hD : ∀n,MeasurableSet (D n))
    (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (hD1 : Tendsto (fun n => (disorderLaw n).real (D n)) atTop (𝓝 1)) :
    Tendsto (fun n => (disorderLaw n).real (C n ∩ D n)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g:=fun n => (disorderLaw n).real (C n)+(disorderLaw n).real (D n)-1)
    (h:=fun _ => (1:ℝ))
  · convert (hC1.add hD1).sub_const 1 using 1; norm_num
  · exact tendsto_const_nhds
  · intro n
    have H := measureReal_union_add_inter (μ:=disorderLaw n) (s:=C n) (hD n)
    have H1 : (disorderLaw n).real (C n ∪ D n)≤1 := measureReal_le_one
    linarith only [H,H1]
  · intro n; exact measureReal_le_one

 theorem finiteGoodEvent_mem (C : ℕ → (n : ℕ) → Set (Disorder n)) (B n : ℕ) (J : Disorder n) :
    J∈finiteGoodEvent C B n ↔ ∀j<B,J∈C j n := by
  induction B with
  | zero => simp [finiteGoodEvent]
  | succ B ih =>
    simp only [finiteGoodEvent,mem_inter_iff,ih]
    constructor
    · rintro ⟨h,hB⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj|rfl
      · exact h j hj
      · exact hB
    · intro h; exact ⟨fun j hj => h j (by omega),h B (by omega)⟩

 theorem finiteGoodEvent_measurable (C : ℕ → (n : ℕ) → Set (Disorder n))
    (hC : ∀j n,MeasurableSet (C j n)) (B n : ℕ) : MeasurableSet (finiteGoodEvent C B n) := by
  induction B with
  | zero => exact MeasurableSet.univ
  | succ B ih => exact ih.inter (hC B n)

 theorem finiteGoodEvent_tendsto (C : ℕ → (n : ℕ) → Set (Disorder n))
    (hC : ∀j n,MeasurableSet (C j n))
    (hC1 : ∀j,Tendsto (fun n => (disorderLaw n).real (C j n)) atTop (𝓝 1)) (B : ℕ) :
    Tendsto (fun n => (disorderLaw n).real (finiteGoodEvent C B n)) atTop (𝓝 1) := by
  induction B with
  | zero => simpa only [finiteGoodEvent,probReal_univ] using (tendsto_const_nhds (x:=(1:ℝ)))
  | succ B ih => exact high_probability_inter _ _ (hC B) ih (hC1 B)

 theorem real_markov_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hm : Measurable f) (h0 : ∀x,0≤f x)
    {a : ℝ} (ha : 0<a) : μ.real {x | a<f x}≤(∫x,f x ∂μ)/a := by
  have hA : MeasurableSet {x | a<f x} := measurableSet_lt measurable_const hm
  apply (le_div_iff₀ ha).mpr
  have H : (∫x,({x | a<f x}).indicator (fun _ => a) x ∂μ)≤∫x,f x ∂μ := by
    apply integral_mono ((integrable_const a).indicator hA) hf
    intro x
    by_cases hx : a<f x
    · simpa only [Set.indicator_of_mem (show x∈{x | a<f x} from hx)] using hx.le
    · simpa only [Set.indicator_of_notMem (show x∉{x | a<f x} from hx)] using h0 x
  simpa only [integral_indicator_const _ hA,smul_eq_mul,mul_comm] using H

 theorem stretched_exp_decay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => Real.exp (-c*levelLogScale n)) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp (stretchedLogScale_tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hc))

 theorem faster_stretched_decay {u : ℝ} (hu : kappa<u) (A K : ℝ) :
    Tendsto (fun n : ℕ => K*Real.exp (A*levelLogScale n-(n:ℝ)^u)) atTop (𝓝 0) := by
  have hu0 : 0<u := (by norm_num [kappa] : (0:ℝ)<kappa).trans hu
  have H : Tendsto (fun n : ℕ => Real.exp (-(1/2:ℝ)*(n:ℝ)^u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (((tendsto_rpow_atTop hu0).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul_atTop_of_neg (by norm_num))
  have H0 : Tendsto (fun n : ℕ => Real.exp (A*levelLogScale n-(n:ℝ)^u)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => (Real.exp_pos _).le)) _ H
    filter_upwards [eventually_const_rpow_le hu A (by norm_num : (0:ℝ)<1/2)] with n hn
    apply Real.exp_le_exp.mpr
    change A*(n:ℝ)^kappa-(n:ℝ)^u≤-(1/2:ℝ)*(n:ℝ)^u
    linarith only [hn]
  simpa only [mul_zero] using H0.const_mul K

 theorem high_probability_small_replica {d : ℕ} (β : ℝ) (S : (n : ℕ) → Finset (ReplicaConfig n d))
    {u : ℝ} (hu : kappa<u) (K A : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (S n) ∂disorderLaw n)≤K*Real.exp (-(n:ℝ)^u)) :
    Tendsto (fun n => (disorderLaw n).real {J | replicaGibbsMass β J (S n)≤Real.exp (-A*levelLogScale n)}) atTop (𝓝 1) := by
  have HC : Tendsto (fun n => (disorderLaw n).real {J | Real.exp (-A*levelLogScale n) < replicaGibbsMass β J (S n)}) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) _ (faster_stretched_decay hu A K)
    filter_upwards [h] with n hn
    refine (real_markov_bound (disorderLaw n) (replicaGibbsMass_integrable β (S n))
      (continuous_replicaGibbsMass β (S n)).measurable (fun J => replicaGibbsMass_nonneg β J (S n)) (Real.exp_pos _)).trans ?_
    calc
      _ ≤ (K*Real.exp (-(n:ℝ)^u))/Real.exp (-A*levelLogScale n) := div_le_div_of_nonneg_right hn (Real.exp_pos _).le
      _ = K*Real.exp (A*levelLogScale n-(n:ℝ)^u) := by rw [mul_div_assoc,← Real.exp_sub]; congr 2; ring
  have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HC
  convert H using 1
  · funext n
    have hM : MeasurableSet {J | Real.exp (-A*levelLogScale n) < replicaGibbsMass β J (S n)} :=
      measurableSet_lt measurable_const (continuous_replicaGibbsMass β (S n)).measurable
    rw [← probReal_compl_eq_one_sub hM]
    congr 1
    ext J
    simp only [mem_ofPred_eq,mem_compl_iff,not_lt]
  · norm_num

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_PathEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

theorem walkWeight_last {n : ℕ} (β : ℝ) (J : Disorder n) (m : ℕ) (x : Config n) (f : Config n → ℝ) :
    (∑ s : Fin m → Config n,FiniteMarkov.walkWeight (heatBath β J) m x s*f ((Fin.cons x s : Fin (m+1) → Config n) (Fin.last m)))=
      ∑ y,discreteKernel β J m x y*f y := by
  induction m generalizing x with
  | zero => simp [FiniteMarkov.walkWeight,discreteKernel]
  | succ m ih =>
    rw [FiniteMarkov.sum_cons]
    have hlast : Fin.last (m+1)=(Fin.last m).succ := rfl
    simp only [FiniteMarkov.walkWeight_cons,hlast,Fin.cons_succ,mul_assoc,← Finset.mul_sum,ih,discreteKernel]
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro y _
    ring

theorem pathFiniteLaw_joint {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (m : ℕ) (f : Config n → Config n → ℝ) :
    (pathFiniteLaw hn β J m).expect (fun s => f (s 0) (s (Fin.last m)))=
      ∑ x,gibbs β J x*∑ y,discreteKernel β J m x y*f x y := by
  unfold FiniteLaw.expect pathFiniteLaw stationaryPathWeight
  rw [FiniteMarkov.sum_cons]
  simp only [FiniteMarkov.pathWeight,Fin.cons_zero,Fin.tail_cons,mul_assoc,← Finset.mul_sum,walkWeight_last]

namespace FiniteLaw
variable {X : Type*} [Fintype X]
theorem prob_mono_on_support (P : FiniteLaw X) {E F : X → Prop}
    (h : ∀x,0<P.weight x → E x → F x) : P.prob E ≤ P.prob F := by
  unfold prob expect
  apply Finset.sum_le_sum
  intro x _
  by_cases hw : 0<P.weight x
  · by_cases hE : E x
    · simp only [ite_eq_left hE,ite_eq_left (h x hw hE),le_refl]
    · simp only [ite_eq_right hE,mul_zero]
      split_ifs <;> positivity
  · have he : P.weight x=0 := le_antisymm (le_of_not_gt hw) (P.nonneg x)
    simp only [he,zero_mul,le_refl]
end FiniteLaw

@[simp] theorem extendPath_at {n m : ℕ} (s : Fin (m+1) → Config n) (k : Fin (m+1)) :
    extendPath s k.val=s k := by simp only [extendPath,dite_eq_left (show k.val ≤ m by omega)]

theorem extendPath_jump {n m : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    (s : Fin (m+1) → Config n) (hs : 0<(pathFiniteLaw hn β J m).weight s) :
    ∀ v k, k < m → |overlap v (extendPath s (k+1))-overlap v (extendPath s k)| ≤ 2/(n:ℝ) := by
  intro v k hk
  simp only [extendPath,dite_eq_left (show k+1 ≤ m by omega),dite_eq_left (show k ≤ m by omega)]
  exact stationaryPathWeight_pos_jump hn β J m s hs v ⟨k,hk⟩

theorem pathFiniteLaw_visit {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (m : ℕ) (V : Config n → Prop) :
    (pathFiniteLaw hn β J m).prob (fun s => ∃k : Fin (m+1),V (s k)) ≤ (m+1)*(gibbsFiniteLaw β J).prob V := by
  refine (FiniteLaw.prob_exists _ _).trans ?_
  have he (k : Fin (m+1)) : (pathFiniteLaw hn β J m).prob (fun s => V (s k))=(gibbsFiniteLaw β J).prob V :=
    pathFiniteLaw_marginal hn β J m k (fun x => if V x then 1 else 0)
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,le_refl]

theorem stationary_sign_crossing_bound {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    (m : ℕ) (v : Config n → Config n) (V : Config n → Prop)
    (hpath : ∀s : Fin (m+1) → Config n,0<(pathFiniteLaw hn β J m).weight s →
      (∀k : Fin (m+1),¬V (s k)) → 0<overlap (v (s 0)) (s (Fin.last m))) :
    (∑ x,gibbs β J x*∑ y,if overlap (v x) y ≤ 0 then discreteKernel β J m x y else 0)  ≤
      (m+1)*(gibbsFiniteLaw β J).prob V := by
  have HE : (∑ x,gibbs β J x*∑ y,if overlap (v x) y ≤ 0 then discreteKernel β J m x y else 0)=
      (pathFiniteLaw hn β J m).prob (fun s => overlap (v (s 0)) (s (Fin.last m)) ≤ 0) := by
    rw [FiniteLaw.prob,pathFiniteLaw_joint hn β J m (fun x y => if overlap (v x) y ≤ 0 then 1 else 0)]
    simp only [mul_ite,mul_one,mul_zero]
  rw [HE]
  refine (FiniteLaw.prob_mono_on_support _ (fun s hs hpass => ?_)).trans (pathFiniteLaw_visit hn β J m V)
  by_contra H
  have hgood : ∀k : Fin (m+1),¬V (s k) := by simpa only [not_exists] using H
  exact (not_lt_of_ge hpass) (hpath s hs hgood)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

theorem bank_no_passage {n : ℕ} (hn : 0<n) (μ : ProbabilityMeasure ℝ)
    (B H s m : ℕ) (t ρ b b' q : ℝ)
    (G : GreedyScaleBounds n B H (B*s) t ρ (2/(n:ℝ)) b b' q)
    (hcount : (B*s)*((4*ρ^8/ρ+1/(n:ℝ))/ρ^4)+(m+1)*(2*(6*(B*s)*ρ^20)/ρ+1/(n:ℝ))^s<1)
    (K : Fin (B*s) → ℕ) (hK : ∀j,0<K j) (z : BankIndex K → Config n)
    (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) (lockingUnion n μ t ρ q b b') z)
    (x : ℕ → Config n)
    (hjump : ∀v k, k < m → |overlap v (x (k+1))-overlap v (x k)| ≤ 2/(n:ℝ))
    (hgood : ∀k ≤ m,¬bankBadVertex K B μ t ρ q b b' z (x k)) :
    0<overlap (initialBankReference (natBankPool K z) (natBankDefault K hK z) B t q (x 0)) (x m) := by
  let pool := natBankPool K z
  let fallback := natBankDefault K hK z
  have hp (i : ℕ) (hi : i<B*s) (v : Config n) (hv : v ∈ pool i) : v ∈ orientedBankPool K z ⟨i,hi⟩ := by
    simpa only [pool,natBankPool,dite_eq_left hi] using hv
  rw [initialBankReference_path]
  apply greedy_no_passage hn μ pool fallback (natBankDefault_mem K hK z) fallback x B H s m t ρ (2/(n:ℝ)) b b' q G hcount hjump
  · intro j hj v hv u hu hc
    exact bank_pool_coverage K B z t q (x u) (fun H => hgood u hu (Or.inl H)) j hj v hv hc
  · intro i j hij hj v hv w hw k hk HS
    have H := bank_pool_no_vertex K z (lockingUnion n μ t ρ q b b') (x k)
      (fun H => hgood k hk (Or.inr H)) ⟨i,hij.trans hj⟩ ⟨j,hj⟩
      (fun he => by have he' : i=j := congrArg Fin.val he; omega) v w (hp i (hij.trans hj) v hv) (hp j hj w hw) (Equiv.refl _)
    apply H
    exact (mem_lockingUnion _ _ _ _ _ _ _ _).mpr (Or.inl (Or.inl HS))
  · intro i k j hik hkj hj v hv u hu w hw
    have Hi := hp i (hik.trans (hkj.trans hj)) v hv
    have Hk := hp k (hkj.trans hj) u hu
    have Hj := hp j hj w hw
    have hki : (⟨k,hkj.trans hj⟩ : Fin (B*s))≠⟨i,hik.trans (hkj.trans hj)⟩ := fun he => by have he' : k=i := congrArg Fin.val he; omega
    have hkj' : (⟨k,hkj.trans hj⟩ : Fin (B*s))≠⟨j,hj⟩ := fun he => by have he' : k=j := congrArg Fin.val he; omega
    have hij' : (⟨i,hik.trans (hkj.trans hj)⟩ : Fin (B*s))≠⟨j,hj⟩ := fun he => by have he' : i=j := congrArg Fin.val he; omega
    constructor
    · intro HS
      exact bank_pool_no_triple K z _ hz _ _ _ hki hkj' hij' u v w Hk Hi Hj
        ((mem_lockingUnion _ _ _ _ _ _ _ _).mpr (Or.inl (Or.inr HS)))
    · intro HS
      exact bank_pool_no_triple K z _ hz _ _ _ hki hkj' hij' u v (flip w) Hk Hi (flip_mem_orientedBankPool K z _ Hj)
        ((mem_lockingUnion _ _ _ _ _ _ _ _).mpr (Or.inl (Or.inr HS)))
  · intro i j hij hj v hv w hw k hk HS
    have HE : ((![v,w,x k] : ReplicaConfig n 3) ∘ Equiv.swap (1:Fin 3) 2)=(![v,x k,w] : ReplicaConfig n 3) := by
      funext a; fin_cases a <;> simp [Equiv.swap_apply_def]
    have H := bank_pool_no_vertex K z (lockingUnion n μ t ρ q b b') (x k)
      (fun H => hgood k hk (Or.inr H)) ⟨i,hij.trans hj⟩ ⟨j,hj⟩
      (fun he => by have he' : i=j := congrArg Fin.val he; omega) v w (hp i (hij.trans hj) v hv) (hp j hj w hw) (Equiv.swap 1 2)
    rw [HE] at H
    exact H ((mem_lockingUnion _ _ _ _ _ _ _ _).mpr (Or.inr HS))

theorem bank_stationary_crossing {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (μ : ProbabilityMeasure ℝ)
    (B H s m : ℕ) (t ρ b b' q : ℝ)
    (G : GreedyScaleBounds n B H (B*s) t ρ (2/(n:ℝ)) b b' q)
    (hcount : (B*s)*((4*ρ^8/ρ+1/(n:ℝ))/ρ^4)+(m+1)*(2*(6*(B*s)*ρ^20)/ρ+1/(n:ℝ))^s<1)
    (K : Fin (B*s) → ℕ) (hK : ∀j,0<K j) (z : BankIndex K → Config n)
    (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) (lockingUnion n μ t ρ q b b') z) :
    (∑x,gibbs β J x*∑y,if overlap (initialBankReference (natBankPool K z) (natBankDefault K hK z) B t q x) y ≤ 0
      then discreteKernel β J m x y else 0)  ≤  (m+1)*(gibbsFiniteLaw β J).prob (bankBadVertex K B μ t ρ q b b' z) := by
  apply stationary_sign_crossing_bound hn β J m _ _
  intro path hpath hg
  have H := bank_no_passage hn μ B H s m t ρ b b' q G hcount K hK z hz (extendPath path)
    (extendPath_jump hn β J path hpath) (fun k hk => by simpa only [extendPath,dite_eq_left hk] using hg ⟨k,by omega⟩)
  have hz0 : (⟨0,show 0 < m+1 by omega⟩ : Fin (m+1))=0 := Fin.ext (by simp)
  simpa only [extendPath,dite_eq_left (show 0 ≤ m by omega),dite_eq_left le_rfl,hz0,Fin.last] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

 theorem scheduledBankSize_pos (c : ℕ → ℝ) (B n : ℕ) {p : ℕ} (j : Fin p) :
    0 < scheduledBankSize c B n j := Nat.ceil_pos.mpr (Real.exp_pos _)

 theorem eventually_exp_dominates_linear (A : ℝ) :
    ∀ᶠ n : ℕ in atTop,A*levelLogScale n≤Real.exp (levelLogScale n) := by
  have H := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 zero_lt_one).comp stretchedLogScale_tendsto).const_mul A
  have H0 : Tendsto (fun n => A*levelLogScale n*Real.exp (-levelLogScale n)) atTop (𝓝 0) := by
    simpa only [levelLogScale,Real.rpow_one,neg_one_mul,mul_assoc,mul_zero,Function.comp_apply] using H
  filter_upwards [H0.eventually_le_const zero_lt_one] with n hn
  have HH := mul_le_mul_of_nonneg_right hn (Real.exp_pos (levelLogScale n)).le
  simpa only [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] using HH

 theorem greedy_level_count_bound {B : ℕ} (hB : 0<B) {t : ℝ} (ht : 0<t) (n : ℕ) :
    (B*greedyBlockCount B t n:ℕ)≤(t/8)*levelLogScale n := by
  have hb : (0:ℝ)<B := by exact_mod_cast hB
  have H := mul_le_mul_of_nonneg_left (Nat.floor_le (show 0≤(t/(8*B))*levelLogScale n by unfold levelLogScale; positivity)) hb.le
  change (B:ℝ)*(greedyBlockCount B t n:ℝ)≤(B:ℝ)*((t/(8*B))*levelLogScale n) at H
  rw [Nat.cast_mul]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

 theorem bank_miss_exp_bound (c L : ℝ) (_index : ℕ) :
    Real.exp (-(Real.exp (-c*L))*(⌈Real.exp ((c+1)*L)⌉₊:ℝ))≤Real.exp (-Real.exp L) := by
  have HK : Real.exp ((c+1)*L)≤(⌈Real.exp ((c+1)*L)⌉₊:ℝ) := Nat.le_ceil _
  apply Real.exp_le_exp.mpr
  have H := mul_le_mul_of_nonneg_left HK (Real.exp_pos (-c*L)).le
  have he : Real.exp (-c*L)*Real.exp ((c+1)*L)=Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at H
  linarith only [H]

 theorem scheduled_bank_coverage_sum {p B n : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0 ≤ c j)
    (hL : 1≤levelLogScale n)
    (hdom : (bankPrefix c B+5)*levelLogScale n≤Real.exp (levelLogScale n)) :
    (∑j : Fin p,(Fintype.card (BankTuple (scheduledBankSize c B n) (blockPrior p B) j):ℝ)*
      (Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n)+
        Real.exp (-(Real.exp (-c (j.val%B)*levelLogScale n))*(scheduledBankSize c B n j))))≤
      2*p*Real.exp (-5*levelLogScale n) := by
  have hK (j : Fin p) : (scheduledBankSize c B n j:ℝ)≤Real.exp ((c (j.val%B)+2)*levelLogScale n) := ceil_exp_bound (hc _) hL
  calc
    _ ≤ ∑_j : Fin p,2*Real.exp (-5*levelLogScale n) := by
      apply Finset.sum_le_sum
      intro j _
      have HA := bankTuple_card_bound hB c (scheduledBankSize c B n) (levelLogScale n) hK j
      have hAj : bankPrefix c (j.val%B)≤bankPrefix c B := bankPrefix_mono c hc (Nat.mod_lt _ hB).le
      have Hmiss : Real.exp (-(Real.exp (-c (j.val%B)*levelLogScale n))*(scheduledBankSize c B n j))≤
          Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n) := by
        refine (bank_miss_exp_bound (c (j.val%B)) (levelLogScale n) 0).trans ?_
        apply Real.exp_le_exp.mpr
        have HH := mul_le_mul_of_nonneg_right (add_le_add hAj (le_refl (5:ℝ))) (by linarith only [hL])
        linarith only [HH,hdom]
      have H := mul_le_mul HA (add_le_add (le_refl (Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n))) Hmiss) (by positivity) (Real.exp_pos _).le
      refine H.trans_eq ?_
      rw [← two_mul,mul_comm (Real.exp _) (2*_),mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

 theorem scheduled_bank_locking_cost {p B n : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0 ≤ c j)
    (hL : 5≤levelLogScale n) (hp : (p:ℝ)≤Real.exp (levelLogScale n)) {v : ℝ}
    (hv0 : 0≤v) (hv : v≤Real.exp (-(3*bankPrefix c B+20)*levelLogScale n)) :
    (8*(Fintype.card (BankIndex (scheduledBankSize c B n (p:=p))):ℝ)^3+
      48*(Fintype.card (BankIndex (scheduledBankSize c B n (p:=p))):ℝ)^2)*v≤Real.exp (-4*levelLogScale n) := by
  let A := bankPrefix c B
  let L := levelLogScale n
  let N : ℝ := Fintype.card (BankIndex (scheduledBankSize c B n (p:=p)))
  have hA : 0≤A := bankPrefix_nonneg c hc B
  have hL0 : 0≤L := by dsimp only [L]; linarith only [hL]
  have hN0 : 0≤N := Nat.cast_nonneg _
  have hN : N≤Real.exp ((A+1)*L) := by
    refine (bankIndex_card_bound hB c hc (scheduledBankSize c B n) hL0
      (fun j => ceil_exp_bound (hc _) (by linarith only [hL]))).trans ?_
    calc
      _ ≤ Real.exp L*Real.exp (A*L) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he1 : 1≤Real.exp ((A+1)*L) := Real.one_le_exp_iff.mpr (by positivity)
  have HN3 : N^3≤Real.exp (3*(A+1)*L) := by
    have H := pow_le_pow_left₀ hN0 hN 3
    simpa only [← Real.exp_nat_mul,Nat.cast_ofNat,mul_assoc] using H
  have HN2 : N^2≤Real.exp (3*(A+1)*L) := by
    have H := pow_le_pow_left₀ hN0 hN 2
    have HH : (Real.exp ((A+1)*L))^2≤(Real.exp ((A+1)*L))^3 := pow_le_pow_right₀ he1 (by decide)
    exact (H.trans HH).trans_eq (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have HC : (8*N^3+48*N^2)*v≤56*Real.exp (-17*L) := by
    calc
      _ ≤ (56*Real.exp (3*(A+1)*L))*Real.exp (-(3*A+20)*L) :=
        mul_le_mul (by linarith only [HN3,HN2]) hv hv0 (by positivity)
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have HE56 : (56:ℝ)≤Real.exp (13*L) := by
    have H := Real.add_one_le_exp (13*L)
    dsimp only [L] at H
    linarith only [H,hL]
  refine HC.trans ?_
  calc
    _ ≤ Real.exp (13*L)*Real.exp (-17*L) := mul_le_mul_of_nonneg_right HE56 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_KernelEvents
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem kernelEvent_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : 0 ≤ kernelEvent β J A k x := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact discreteKernel_nonneg β J k x y
  · exact le_rfl

theorem kernelEvent_le_one {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] (k : ℕ) (x : Config n) : kernelEvent β J A k x ≤ 1 := by
  rw [← discreteKernel_sum hn β J k x]
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · exact discreteKernel_nonneg β J k x y

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_TVSignBridge
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem finite_event_le_tv {Ω : Type*} [Fintype Ω] (p q : Ω → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) (A : Ω → Prop) [DecidablePred A] :
    (∑ x, if A x then q x else 0)-(∑ x, if A x then p x else 0) ≤
      (1/2:ℝ)*∑ x, |p x-q x| := by
  have hsum : ∑ x, (q x-p x) = 0 := by rw [Finset.sum_sub_distrib,hq,hp,sub_self]
  have ht (x : Ω) : 2*(if A x then q x-p x else 0)-(q x-p x) ≤ |q x-p x| := by
    by_cases hx : A x
    · simp only [ite_eq_left hx]
      linarith [le_abs_self (q x-p x)]
    · simp only [ite_eq_right hx,mul_zero,zero_sub]
      exact neg_le_abs (q x-p x)
  have H := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Ω)) => ht x)
  have he : (∑ x, if A x then q x-p x else 0) =
      (∑ x, if A x then q x else 0)-(∑ x, if A x then p x else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,hsum,sub_zero,he] at H
  have ha : (∑ x, |q x-p x|) = ∑ x, |p x-q x| := by
    apply Finset.sum_congr rfl
    intro x _
    exact abs_sub_comm _ _
  rw [ha] at H
  linarith

theorem gibbs_nonpositive_overlap_mass {n : ℕ} (β : ℝ) (J : Disorder n) (v : Config n) :
    (1/2:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then gibbs β J y else 0 := by
  classical
  let e : Config n ≃ Config n := ⟨flip,flip,flip_flip,flip_flip⟩
  have he : (∑ y : Config n, if -overlap v y ≤ 0 then gibbs β J y else 0) =
      ∑ y : Config n, if overlap v y ≤ 0 then gibbs β J y else 0 := by
    calc
      _ = ∑ y : Config n, if overlap v (e y) ≤ 0 then gibbs β J (e y) else 0 := by
        change _ = ∑ y : Config n, if overlap v (flip y) ≤ 0 then gibbs β J (flip y) else 0
        simp only [overlap_flip_right,gibbs_flip]
      _ = _ := Equiv.sum_comp e (fun y => if overlap v y ≤ 0 then gibbs β J y else 0)
  have ht (y : Config n) : gibbs β J y ≤
      (if overlap v y ≤ 0 then gibbs β J y else 0)+
      (if -overlap v y ≤ 0 then gibbs β J y else 0) := by
    by_cases h : overlap v y ≤ 0
    · simp only [ite_eq_left h]
      split_ifs <;> linarith [gibbs_pos β J y]
    · have h' : -overlap v y ≤ 0 := by linarith [lt_of_not_ge h]
      simp only [ite_eq_right h,ite_eq_left h',zero_add,le_refl]
  have H := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) => ht y)
  rw [gibbs_sum,Finset.sum_add_distrib,he] at H
  linarith

theorem discrete_sign_mass_of_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (x v : Config n) (k : ℕ) (hTV : discreteDistance β J x k ≤ (1/4:ℝ)) :
    (1/4:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then discreteKernel β J k x y else 0 := by
  have H := finite_event_le_tv (discreteKernel β J k x) (gibbs β J)
    (discreteKernel_sum hn β J k x) (gibbs_sum β J) (fun y => overlap v y ≤ 0)
  have HG := gibbs_nonpositive_overlap_mass β J v
  change _ ≤ discreteDistance β J x k at H
  linarith

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_Uniformization
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem clockWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ clockWeight a k := by
  unfold clockWeight
  positivity

theorem clockWeight_hasSum (a : ℝ) : HasSum (clockWeight a) 1 := by
  have H := (NormedSpace.expSeries_div_hasSum_exp a).mul_left (Real.exp (-a))
  rw [← Real.exp_eq_exp_ℝ,← Real.exp_add,neg_add_cancel,Real.exp_zero] at H
  unfold clockWeight
  simpa only [mul_div_assoc] using H

theorem clockWeight_sum (a : ℝ) : ∑' k : ℕ, clockWeight a k = 1 := (clockWeight_hasSum a).tsum_eq

theorem uniformization_summable {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (x y : Config n) :
    Summable (fun k : ℕ => clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (clockWeight_nonneg (by positivity) k)
    (discreteKernel_nonneg β J k x y)) (fun k => ?_) (clockWeight_hasSum ((n:ℝ)*t)).summable
  exact mul_le_of_le_one_right (clockWeight_nonneg (by positivity) k) (discreteKernel_le_one hn β J k x y)

theorem continuousKernel_eq_clock {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ)
    (x y : Config n) : continuousKernel β J t x y =
      ∑' k : ℕ, clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y := by
  simp only [continuousKernel,clockWeight,neg_mul]

theorem continuousKernel_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0 ≤ t)
    (x y : Config n) : 0 ≤ continuousKernel β J t x y := by
  rw [continuousKernel_eq_clock]
  apply tsum_nonneg
  intro k
  apply mul_nonneg
  · exact clockWeight_nonneg (by positivity) k
  · exact discreteKernel_nonneg β J k x y

theorem continuousKernel_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (x : Config n) : ∑ y : Config n, continuousKernel β J t x y = 1 := by
  classical
  simp_rw [continuousKernel_eq_clock]
  rw [← Summable.tsum_finsetSum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) =>
    uniformization_summable hn β J ht x y)]
  simp_rw [← Finset.mul_sum,discreteKernel_sum hn,mul_one]
  exact clockWeight_sum _

theorem continuous_sign_mass_of_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (x v : Config n) {t : ℝ} (ht : 0 ≤ t) (hTV : continuousDistance β J x t ≤ (1/4:ℝ)) :
    (1/4:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then continuousKernel β J t x y else 0 := by
  have H := finite_event_le_tv (continuousKernel β J t x) (gibbs β J)
    (continuousKernel_sum hn β J ht x) (gibbs_sum β J) (fun y => overlap v y ≤ 0)
  have HG := gibbs_nonpositive_overlap_mass β J v
  change _ ≤ continuousDistance β J x t at H
  linarith

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ClockTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem clockWeight_succ_mul (a : ℝ) (k : ℕ) :
    ((k+1:ℕ):ℝ)*clockWeight a (k+1) = a*clockWeight a k := by
  unfold clockWeight
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  have h1 : (k:ℝ)+1 ≠ 0 := by positivity
  have h2 : (k.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem clockWeight_mean_hasSum (a : ℝ) : HasSum (fun k : ℕ => (k:ℝ)*clockWeight a k) a := by
  have H := (clockWeight_hasSum a).mul_left a
  rw [mul_one] at H
  have HH : HasSum (fun k : ℕ => ((k+1:ℕ):ℝ)*clockWeight a (k+1)) a := by
    simpa only [clockWeight_succ_mul] using H
  have HHH := (hasSum_nat_add_iff (f := fun k : ℕ => (k:ℝ)*clockWeight a k) (g := a) 1).mp HH
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,add_zero] using HHH

theorem clockWeight_tail_summable {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    Summable (fun k : ℕ => if m < k then clockWeight a k else 0) := by
  apply Summable.of_nonneg_of_le _ _ (clockWeight_hasSum a).summable
  · intro k; split_ifs
    · exact clockWeight_nonneg ha k
    · exact le_refl 0
  · intro k; split_ifs
    · exact le_refl _
    · exact clockWeight_nonneg ha k

theorem clockWeight_tail_le {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : 0 < m) :
    (∑' k : ℕ, if m < k then clockWeight a k else 0) ≤ a/(m:ℝ) := by
  have H := ((clockWeight_tail_summable ha m).mul_left (m:ℝ)).tsum_le_tsum
    (fun k => show (m:ℝ)*(if m < k then clockWeight a k else 0) ≤ (k:ℝ)*clockWeight a k from by
      split_ifs with hk
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_of_lt hk) (clockWeight_nonneg ha k)
      · simp only [mul_zero]; exact mul_nonneg (by positivity) (clockWeight_nonneg ha k))
    (clockWeight_mean_hasSum a).summable
  rw [tsum_mul_left,(clockWeight_mean_hasSum a).tsum_eq] at H
  exact (le_div_iff₀ (show (0:ℝ) < m by exact_mod_cast hm)).mpr (by simpa only [mul_comm] using H)

theorem attempt_horizon_tail (n : ℕ) (L : ℝ) :
    (∑' k : ℕ, if ⌈Real.exp (2*L)⌉₊ < k then clockWeight ((n:ℝ)*Real.exp L) k else 0) ≤
      (n:ℝ)*Real.exp (-L) := by
  have hExp := Real.exp_pos (2*L)
  have hm : 0 < ⌈Real.exp (2*L)⌉₊ := Nat.ceil_pos.mpr hExp
  have hceil : Real.exp (2*L) ≤ (⌈Real.exp (2*L)⌉₊:ℝ) := Nat.le_ceil _
  calc
    _ ≤ ((n:ℝ)*Real.exp L)/(⌈Real.exp (2*L)⌉₊:ℝ) := clockWeight_tail_le (by positivity) hm
    _ ≤ ((n:ℝ)*Real.exp L)/Real.exp (2*L) := div_le_div_of_nonneg_left (by positivity) hExp hceil
    _ = (n:ℝ)*Real.exp (-L) := by
      rw [mul_div_assoc,← Real.exp_sub]
      congr 2
      ring

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ContinuousCrossing
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem clock_kernelEvent_summable {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] {a : ℝ} (ha : 0 ≤ a) (x : Config n) :
    Summable (fun k : ℕ => clockWeight a k*kernelEvent β J A k x) := by
  apply Summable.of_nonneg_of_le _ _ (clockWeight_hasSum a).summable
  · intro k
    exact mul_nonneg (clockWeight_nonneg ha k) (kernelEvent_nonneg _ _ _ _ _)
  · intro k
    exact mul_le_of_le_one_right (clockWeight_nonneg ha k) (kernelEvent_le_one hn β J A k x)

theorem continuous_event_eq_clock {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] {t : ℝ} (ht : 0 ≤ t) (x : Config n) :
    (∑ y : Config n, if A y then continuousKernel β J t x y else 0) =
      ∑' k : ℕ, clockWeight ((n:ℝ)*t) k*kernelEvent β J A k x := by
  have he (y : Config n) : (if A y then continuousKernel β J t x y else 0) =
      ∑' k : ℕ, if A y then clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y else 0 := by
    by_cases hy : A y
    · simp only [ite_eq_left hy,continuousKernel_eq_clock]
    · simp only [ite_eq_right hy,tsum_zero]
  have hs (y : Config n) : Summable (fun k : ℕ =>
      if A y then clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y else 0) := by
    by_cases hy : A y
    · simp only [ite_eq_left hy]
      exact uniformization_summable hn β J ht x y
    · simp only [ite_eq_right hy]
      exact summable_zero
  simp_rw [he]
  rw [← Summable.tsum_finsetSum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) => hs y)]
  simp only [kernelEvent,Finset.mul_sum,mul_ite,mul_zero]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ClockEndpoint
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem discreteMixedMass_le_sign {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (k : ℕ)
    (v : Config n → Config n) : discreteMixedMass β J k ≤
      4*∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x := by
  unfold discreteMixedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : discreteDistance β J x k≤(1/4:ℝ)
  · simp only [ite_eq_left h]
    have H := discrete_sign_mass_of_tv hn β J x (v x) k h
    change (1/4:ℝ)≤kernelEvent β J (fun y => overlap (v x) y≤0) k x at H
    have := mul_le_mul_of_nonneg_left H (gibbs_pos β J x).le
    linarith only [this]
  · simp only [ite_eq_right h]
    exact mul_nonneg (by norm_num) (mul_nonneg (gibbs_pos β J x).le (kernelEvent_nonneg _ _ _ _ _))

theorem continuousMixedMass_le_sign {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0≤t)
    (v : Config n → Config n) : continuousMixedMass β J t ≤
      4*∑x,gibbs β J x*∑y,if overlap (v x) y≤0 then continuousKernel β J t x y else 0 := by
  unfold continuousMixedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : continuousDistance β J x t≤(1/4:ℝ)
  · simp only [ite_eq_left h]
    have H := continuous_sign_mass_of_tv hn β J x (v x) ht h
    have := mul_le_mul_of_nonneg_left H (gibbs_pos β J x).le
    linarith only [this]
  · simp only [ite_eq_right h]
    apply mul_nonneg (by norm_num)
    apply mul_nonneg (gibbs_pos β J x).le
    apply Finset.sum_nonneg
    intro y _
    split_ifs
    · exact continuousKernel_nonneg β J ht x y
    · exact le_rfl

theorem averaged_sign_clock {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0≤t)
    (v : Config n → Config n) :
    (∑x,gibbs β J x*∑y,if overlap (v x) y≤0 then continuousKernel β J t x y else 0)=
      ∑' k : ℕ,clockWeight ((n:ℝ)*t) k*(∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x) := by
  simp_rw [continuous_event_eq_clock hn β J _ ht]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun x (_ : x∈(Finset.univ : Finset (Config n))) =>
    (clock_kernelEvent_summable hn β J (fun y => overlap (v x) y≤0) (by positivity) x).mul_left (gibbs β J x))]
  congr 1
  funext k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

 theorem averaged_kernelEvent_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Config n → Prop) (k : ℕ) :
    0≤∑x,gibbs β J x*kernelEvent β J (A x) k x := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (gibbs_pos β J x).le (kernelEvent_nonneg _ _ _ _ _)

 theorem averaged_kernelEvent_le_one {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (A : Config n → Config n → Prop) (k : ℕ) :
    (∑x,gibbs β J x*kernelEvent β J (A x) k x)≤1 := by
  rw [← gibbs_sum β J]
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_of_le_one_right (gibbs_pos β J x).le (kernelEvent_le_one hn β J _ _ _)

theorem averaged_sign_clock_bound {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0≤t)
    (v : Config n → Config n) (m : ℕ) {E : ℝ} (hE : 0≤E)
    (h : ∀k ≤ m,(∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x)≤E) :
    (∑x,gibbs β J x*∑y,if overlap (v x) y≤0 then continuousKernel β J t x y else 0)≤
      E+∑' k : ℕ,if m<k then clockWeight ((n:ℝ)*t) k else 0 := by
  rw [averaged_sign_clock hn β J ht v]
  have ha : 0≤(n:ℝ)*t := by positivity
  have hs : Summable (fun k : ℕ => clockWeight ((n:ℝ)*t) k*
      (∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x)) := by
    apply Summable.of_nonneg_of_le _ _ (clockWeight_hasSum ((n:ℝ)*t)).summable
    · intro k; exact mul_nonneg (clockWeight_nonneg ha k) (averaged_kernelEvent_nonneg _ _ _ _)
    · intro k; exact mul_le_of_le_one_right (clockWeight_nonneg ha k) (averaged_kernelEvent_le_one hn _ _ _ _)
  have HB := hs.tsum_le_tsum (g := fun k => clockWeight ((n:ℝ)*t) k*E+(if m<k then clockWeight ((n:ℝ)*t) k else 0))
    (fun k => by
      by_cases hk : m<k
      · simp only [ite_eq_left hk]
        have H := mul_le_of_le_one_right (clockWeight_nonneg ha k) (averaged_kernelEvent_le_one hn β J (fun x y => overlap (v x) y≤0) k)
        linarith only [H,mul_nonneg (clockWeight_nonneg ha k) hE]
      · simp only [ite_eq_right hk,add_zero]
        exact mul_le_mul_of_nonneg_left (h k (le_of_not_gt hk)) (clockWeight_nonneg ha k))
    (((clockWeight_hasSum ((n:ℝ)*t)).summable.mul_right E).add (clockWeight_tail_summable ha m))
  simpa only [Summable.tsum_add ((clockWeight_hasSum ((n:ℝ)*t)).summable.mul_right E) (clockWeight_tail_summable ha m),tsum_mul_right,clockWeight_sum,one_mul] using HB

 theorem mixedMass_bounds_of_crossing {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (L E : ℝ)
    (hL : 0≤L) (hE : 0≤E) (v : Config n → Config n)
    (h : ∀k≤⌈Real.exp (2*L)⌉₊,(∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) k x)≤E) :
    continuousMixedMass β J (Real.exp L)≤4*(E+(n:ℝ)*Real.exp (-L)) ∧
    discreteMixedMass β J ⌊Real.exp L⌋₊≤4*E := by
  constructor
  · refine (continuousMixedMass_le_sign hn β J (Real.exp_pos L).le v).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (averaged_sign_clock_bound hn β J (Real.exp_pos L).le v _ hE h).trans
      (add_le_add le_rfl (attempt_horizon_tail n L))
  · refine (discreteMixedMass_le_sign hn β J ⌊Real.exp L⌋₊ v).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply h
    exact (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hL]))).trans (Nat.floor_le_ceil _)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_DynamicsMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem continuous_coupling {n : ℕ} (i j : Fin n) : Continuous (fun J : Disorder n => coupling J i j) := by
  unfold coupling
  split_ifs <;> first | exact continuous_apply _ | exact continuous_const

theorem continuous_localField {n : ℕ} (x : Config n) (i : Fin n) : Continuous (fun J : Disorder n => localField J x i) := by
  unfold localField
  apply Continuous.div_const
  exact continuous_finsetSum _ (fun j _ => (continuous_coupling i j).mul continuous_const)

theorem continuous_heatBath {n : ℕ} (β : ℝ) (x y : Config n) : Continuous (fun J : Disorder n => heatBath β J x y) := by
  unfold heatBath
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  split_ifs
  · apply Continuous.div
    · exact (continuous_const.mul (continuous_localField x i)).rexp
    · exact continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul (continuous_localField x i)))
    · intro J; exact mul_ne_zero (by norm_num) (Real.cosh_pos _).ne'
  · exact continuous_const

theorem continuous_discreteKernel {n : ℕ} (β : ℝ) (k : ℕ) (x y : Config n) :
    Continuous (fun J : Disorder n => discreteKernel β J k x y) := by
  induction k generalizing x y with
  | zero => exact continuous_const
  | succ k ih =>
    exact continuous_finsetSum _ (fun z _ => (continuous_heatBath β x z).mul (ih z y))

theorem measurable_continuousKernel {n : ℕ} (β : ℝ) (t : ℝ) (x y : Config n) :
    Measurable (fun J : Disorder n => continuousKernel β J t x y) := by
  exact Measurable.tsum (fun k => measurable_const.mul (continuous_discreteKernel β k x y).measurable)

theorem continuous_discreteDistance {n : ℕ} (β : ℝ) (k : ℕ) (x : Config n) :
    Continuous (fun J : Disorder n => discreteDistance β J x k) := by
  exact continuous_const.mul (continuous_finsetSum _ (fun y _ => ((continuous_discreteKernel β k x y).sub (continuous_gibbs β y)).abs))

theorem measurable_continuousDistance {n : ℕ} (β : ℝ) (t : ℝ) (x : Config n) :
    Measurable (fun J : Disorder n => continuousDistance β J x t) := by
  exact measurable_const.mul (Finset.measurable_sum _ (fun y _ => ((measurable_continuousKernel β t x y).sub (continuous_gibbs β y).measurable).abs))

theorem measurable_gibbs_predicate_mass {n : ℕ} (β : ℝ) (E : Disorder n → Config n → Prop)
    (hE : ∀x,MeasurableSet {J | E J x}) :
    Measurable (fun J => ∑x,if E J x then gibbs β J x else 0) := by
  exact Finset.measurable_sum _ (fun x _ => Measurable.ite (hE x) (continuous_gibbs β x).measurable measurable_const)

theorem gibbs_predicate_mass_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    0≤∑x,if E x then gibbs β J x else 0 := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact (gibbs_pos β J x).le | exact le_rfl

theorem gibbs_predicate_mass_le_one {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (∑x,if E x then gibbs β J x else 0)≤1 := by
  rw [← gibbs_sum β J]
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> first | exact le_rfl | exact (gibbs_pos β J x).le

theorem integrable_gibbs_predicate_mass {n : ℕ} (β : ℝ) (E : Disorder n → Config n → Prop)
    (hE : ∀x,MeasurableSet {J | E J x}) :
    Integrable (fun J => ∑x,if E J x then gibbs β J x else 0) (disorderLaw n) := by
  apply (integrable_const (1:ℝ)).mono' (measurable_gibbs_predicate_mass β E hE).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs,abs_of_nonneg (gibbs_predicate_mass_nonneg β J _)] using gibbs_predicate_mass_le_one β J (E J)

theorem discreteMixedMass_integrable (n : ℕ) (β : ℝ) (k : ℕ) :
    Integrable (fun J : Disorder n => discreteMixedMass β J k) (disorderLaw n) :=
  integrable_gibbs_predicate_mass β _ (fun x => measurableSet_le (continuous_discreteDistance β k x).measurable measurable_const)

theorem continuousMixedMass_integrable (n : ℕ) (β : ℝ) (t : ℝ) :
    Integrable (fun J : Disorder n => continuousMixedMass β J t) (disorderLaw n) :=
  integrable_gibbs_predicate_mass β _ (fun x => measurableSet_le (measurable_continuousDistance β t x) measurable_const)

theorem gibbs_predicate_mass_compl {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (∑x,if ¬E x then gibbs β J x else 0)=1-∑x,if E x then gibbs β J x else 0 := by
  rw [← gibbs_sum β J,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

theorem discreteBadMass_eq_one_sub (β : ℝ) (n : ℕ) :
    discreteBadMass β n=1-∫J,discreteMixedMass β J ⌊timeScale n⌋₊ ∂disorderLaw n := by
  have he (J : Disorder n) : (∑x,if (1/4:ℝ)<discreteDistance β J x ⌊timeScale n⌋₊ then gibbs β J x else 0)=
      1-discreteMixedMass β J ⌊timeScale n⌋₊ := by
    simpa only [not_le,discreteMixedMass] using gibbs_predicate_mass_compl β J (fun x => discreteDistance β J x ⌊timeScale n⌋₊≤(1/4:ℝ))
  unfold discreteBadMass
  simp_rw [he]
  rw [integral_sub (integrable_const 1) (discreteMixedMass_integrable n β _)]
  simp

theorem continuousBadMass_eq_one_sub (β : ℝ) (n : ℕ) :
    continuousBadMass β n=1-∫J,continuousMixedMass β J (timeScale n) ∂disorderLaw n := by
  have he (J : Disorder n) : (∑x,if (1/4:ℝ) < continuousDistance β J x (timeScale n) then gibbs β J x else 0)=
      1-continuousMixedMass β J (timeScale n) := by
    simpa only [not_le,continuousMixedMass] using gibbs_predicate_mass_compl β J (fun x => continuousDistance β J x (timeScale n)≤(1/4:ℝ))
  unfold continuousBadMass
  simp_rw [he]
  rw [integral_sub (integrable_const 1) (continuousMixedMass_integrable n β _)]
  simp

theorem main_of_quenched_mixed_bounds (β : ℝ) (C : (n : ℕ) → Set (Disorder n))
    (hC : ∀n,MeasurableSet (C n)) (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (e : ℕ → ℝ) (he : ∀n,0≤e n) (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n : ℕ in atTop,∀J∈C n,continuousMixedMass β J (timeScale n)≤e n ∧
      discreteMixedMass β J ⌊timeScale n⌋₊≤e n) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  have hcomp : Tendsto (fun n => (disorderLaw n).real (C n)ᶜ) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds (x:=(1:ℝ))).sub hC1
    simpa only [measureReal_compl (hC _),probReal_univ,sub_self] using H
  have hlim := he0.add hcomp
  simp only [add_zero] at hlim
  have HC : Tendsto (fun n => ∫J,continuousMixedMass β J (timeScale n) ∂disorderLaw n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun J => gibbs_predicate_mass_nonneg β J _))) _ hlim
    filter_upwards [hbound] with n hn
    apply integral_le_off_exception (continuousMixedMass_integrable n β _) (hC n).compl (he n)
      (fun J => gibbs_predicate_mass_le_one β J _)
    intro J hJ
    exact (hn J (by simpa only [mem_compl_iff,not_not] using hJ)).1
  have HD : Tendsto (fun n => ∫J,discreteMixedMass β J ⌊timeScale n⌋₊ ∂disorderLaw n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun J => gibbs_predicate_mass_nonneg β J _))) _ hlim
    filter_upwards [hbound] with n hn
    apply integral_le_off_exception (discreteMixedMass_integrable n β _) (hC n).compl (he n)
      (fun J => gibbs_predicate_mass_le_one β J _)
    intro J hJ
    exact (hn J (by simpa only [mem_compl_iff,not_not] using hJ)).2
  constructor
  · have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HC
    simpa only [← continuousBadMass_eq_one_sub,sub_zero] using H
  · have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HD
    simpa only [← discreteBadMass_eq_one_sub,sub_zero] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GreedyEventual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

 theorem greedyBlockCount_eventual {B : ℕ} (hB : 0<B) {t : ℝ} (ht : 0<t) :
    ∀ᶠ n : ℕ in atTop,0<greedyBlockCount B t n ∧
      (t/(8*B))*levelLogScale n/2≤(greedyBlockCount B t n:ℝ) := by
  have hc : 0<t/(8*B) := by positivity
  have H := stretchedLogScale_tendsto.const_mul_atTop hc
  filter_upwards [H.eventually_ge_atTop 2] with n hn
  change 2≤(t/(8*B))*levelLogScale n at hn
  constructor
  · exact Nat.floor_pos.mpr (by linarith only [hn])
  · have h := Nat.lt_floor_add_one ((t/(8*B))*levelLogScale n)
    change _≤(⌊(t/(8*B))*levelLogScale n⌋₊:ℝ)
    linarith only [h,hn]

 theorem greedyScale_eventual {B H : ℕ} (hB : 0<B) (hHB : H<B) {t b b' q : ℝ}
    (ht : 0<t) (hb : 0<b) (hpack : ⌈2/b^2⌉₊≤H) (hpack' : 3*t<b^2/2)
    (hcut : 3*t<b) (hcut' : 2*t<b') (hh : 2*t<q) :
    ∀ᶠ n : ℕ in atTop,GreedyScaleBounds n B H (B*greedyBlockCount B t n) t (levelRho n) (2/(n:ℝ)) b b' q := by
  have HF := greedySlack_tendsto t
  have HFq := HF.const_mul 2
  have HW := levelRho_tendsto.pow 8
  filter_upwards [eventually_gt_atTop (0:ℕ),greedyBlockCount_eventual hB ht,
    levelRho_tendsto.eventually_lt_const zero_lt_one,
    (greedySlack_div_tendsto t).eventually_lt_const zero_lt_one,
    HF.eventually_lt_const ht,HF.eventually_lt_const (sub_pos.mpr hcut'),
    HFq.eventually_lt_const (by simpa only [mul_zero] using sub_pos.mpr hh),
    HW.eventually_lt_const (by simpa only [zero_pow (by decide : 8≠0)] using half_pos ht)] with n hn hs hρ1 hF hFt hFb hFq hW
  apply greedyScale_of_slack hn hB hHB hs.1 hpack ht hb hpack' hcut (levelRho_pos hn) hρ1
    (levelRho_eta hn) (levelRho_inv hn) (greedyBlockCount_upper hn hB ht)
  · exact (div_lt_one (pow_pos (levelRho_pos hn) 8)).mp hF
  · exact hFt
  · linarith only [hFb]
  · linarith only [hFq]
  · exact hW

 theorem greedy_grid_mass_bound {n B : ℕ} (hn : 0<n) (hB : 0<B) {t : ℝ} (ht : 0<t) :
    (B*greedyBlockCount B t n:ℕ)*((4*(levelRho n)^8/(levelRho n)+1/(n:ℝ))/(levelRho n)^4) ≤
      (t/8)*(4*(levelRho n)^2+(levelRho n)^9995) := by
  have hp := greedyBlockCount_upper hn hB ht
  have he : (B*greedyBlockCount B t n:ℕ)*((4*(levelRho n)^8/(levelRho n)+1/(n:ℝ))/(levelRho n)^4)=
      ((B*greedyBlockCount B t n:ℕ)*levelRho n)*(4*(levelRho n)^2+(levelRho n)^9995) := by
    rw [levelRho_inv hn]
    have hρ := (levelRho_pos hn).ne'
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right hp (by have := (levelRho_pos hn).le; positivity)

 theorem greedy_grid_window_bound {n B : ℕ} (hn : 0<n) (hB : 0<B) {t : ℝ} (ht : 0<t) :
    2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)+1/(n:ℝ) ≤
      (3*t/2)*(levelRho n)^18+(levelRho n)^10000 := by
  have hp := greedyBlockCount_upper hn hB ht
  rw [levelRho_inv hn]
  have he : 2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)=
      ((B*greedyBlockCount B t n:ℕ)*levelRho n)*(12*(levelRho n)^18) := by
    have hρ := (levelRho_pos hn).ne'
    field_simp
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_right hp (show 0≤12*(levelRho n)^18 by positivity)
  nlinarith only [h]

 theorem horizon_size_bound {L : ℝ} (hL : 0≤L) : (⌈Real.exp (2*L)⌉₊:ℝ)+1≤3*Real.exp (2*L) := by
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (2*L)).le
  have hh : 1≤Real.exp (2*L) := Real.one_le_exp_iff.mpr (by positivity)
  linarith only [hc,hh]

 theorem greedy_count_eventual {B : ℕ} (hB : 0<B) {t : ℝ} (ht : 0<t) :
    ∀ᶠ n : ℕ in atTop,∀m≤⌈Real.exp (2*levelLogScale n)⌉₊,
      (B*greedyBlockCount B t n:ℕ)*((4*(levelRho n)^8/(levelRho n)+1/(n:ℝ))/(levelRho n)^4)+
        (m+1)*(2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)+1/(n:ℝ))^(greedyBlockCount B t n)<1 := by
  let c : ℝ := t/(8*B)
  have hc : 0 < c := by dsimp only [c]; positivity
  have HM : Tendsto (fun n => (t/8)*(4*(levelRho n)^2+(levelRho n)^9995)) atTop (𝓝 0) := by
    convert (((levelRho_tendsto.pow 2).const_mul 4).add (levelRho_tendsto.pow 9995)).const_mul (t/8) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have HW : Tendsto (fun n => (3*t/2)*(levelRho n)^18+(levelRho n)^10000) atTop (𝓝 0) := by
    convert ((levelRho_tendsto.pow 18).const_mul (3*t/2)).add (levelRho_tendsto.pow 10000) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have HE : Tendsto (fun n => 3*Real.exp (-2*levelLogScale n)) atTop (𝓝 0) := by
    have H := (Real.tendsto_exp_atBot.comp (stretchedLogScale_tendsto.const_mul_atTop_of_neg (by norm_num : (-2:ℝ)<0))).const_mul 3
    simpa only [mul_zero,levelLogScale,Function.comp_apply] using H
  filter_upwards [eventually_gt_atTop (0:ℕ),greedyBlockCount_eventual hB ht,
    HM.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    HW.eventually_le_const (Real.exp_pos (-8/c)),HE.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with n hn hs hm hw he
  intro m hmn
  have hρ := levelRho_pos hn
  let γ : ℝ := 2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)+1/(n:ℝ)
  have hγ : 0≤γ := by dsimp only [γ]; positivity
  have hγ' : γ≤Real.exp (-8/c) := (greedy_grid_window_bound hn hB ht).trans hw
  have hpow : γ^(greedyBlockCount B t n)≤Real.exp (-4*levelLogScale n) := by
    calc
      _ ≤ (Real.exp (-8/c))^(greedyBlockCount B t n) := pow_le_pow_left₀ hγ hγ' _
      _ = Real.exp ((greedyBlockCount B t n:ℝ)*(-8/c)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonpos_right hs.2 (show -8/c≤0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hc.le)
        change _≤(c*levelLogScale n/2)*(-8/c) at hh
        have hz : (c*levelLogScale n/2)*(-8/c)=-4*levelLogScale n := by field_simp; ring
        rw [hz] at hh
        exact hh)
  have hM : (m:ℝ)+1≤3*Real.exp (2*levelLogScale n) := by
    have hk : (m:ℝ)≤⌈Real.exp (2*levelLogScale n)⌉₊ := by exact_mod_cast hmn
    exact (add_le_add hk (le_refl (1:ℝ))).trans (horizon_size_bound (L:=levelLogScale n) (by unfold levelLogScale; positivity))
  have hprod : ((m:ℝ)+1)*γ^(greedyBlockCount B t n)≤3*Real.exp (-2*levelLogScale n) := by
    calc
      _ ≤ (3*Real.exp (2*levelLogScale n))*Real.exp (-4*levelLogScale n) := mul_le_mul hM hpow (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hb := greedy_grid_mass_bound hn hB ht
  linarith only [hb,hm,hprod,he]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_IdentityDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem scheduled_bank_total {n p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0 ≤ c j)
    (hL : 5≤levelLogScale n) (hp : (p:ℝ)≤Real.exp (levelLogScale n))
    (hdom : (bankPrefix c B+5)*levelLogScale n≤Real.exp (levelLogScale n))
    {v : ℝ} (hv0 : 0≤v) (hv : v≤Real.exp (-(3*bankPrefix c B+20)*levelLogScale n)) :
    (8*(Fintype.card (BankIndex (scheduledBankSize c B n (p:=p))):ℝ)^3+
      48*(Fintype.card (BankIndex (scheduledBankSize c B n (p:=p))):ℝ)^2)*v+
    (∑j : Fin p,(Fintype.card (BankTuple (scheduledBankSize c B n) (blockPrior p B) j):ℝ)*
      (Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n)+
        Real.exp (-(Real.exp (-c (j.val%B)*levelLogScale n))*(scheduledBankSize c B n j))))≤
      3*Real.exp (-4*levelLogScale n) := by
  have HL := scheduled_bank_locking_cost hB c hc hL hp hv0 hv
  have HC := scheduled_bank_coverage_sum (p:=p) hB c hc (by linarith only [hL]) hdom
  have HP : 2*(p:ℝ)*Real.exp (-5*levelLogScale n)≤2*Real.exp (-4*levelLogScale n) := by
    calc
      _ ≤ 2*Real.exp (levelLogScale n)*Real.exp (-5*levelLogScale n) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  linarith only [HL,HC,HP]

 theorem identity_quenched_bound {n B H : ℕ} (hn : 0<n) (hB : 0<B)
    (β : ℝ) (J : Disorder n) (μ : ProbabilityMeasure ℝ) (t b b' q : ℝ)
    (c : ℕ → ℝ) (hc : ∀j,0 ≤ c j)
    (hcov : ∀j<B,∀E : Config n → Prop,
      (gibbsFiniteLaw β J).prob (fun x => E x ∧ (gibbsFiniteLaw β J).prob (fun y => E y ∧ q≤|overlap x y|)<Real.exp (-c j*levelLogScale n))≤
        Real.exp (-(bankPrefix c j+5)*levelLogScale n))
    (hv : replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b')≤Real.exp (-(3*bankPrefix c B+20)*levelLogScale n))
    (hL : 5≤levelLogScale n)
    (hp : (B*greedyBlockCount B t n:ℕ)≤Real.exp (levelLogScale n))
    (hdom : (bankPrefix c B+5)*levelLogScale n≤Real.exp (levelLogScale n))
    (hsmall : 3*Real.exp (-4*levelLogScale n)<1)
    (G : GreedyScaleBounds n B H (B*greedyBlockCount B t n) t (levelRho n) (2/(n:ℝ)) b b' q)
    (hcount : ∀m≤⌈Real.exp (2*levelLogScale n)⌉₊,
      (B*greedyBlockCount B t n:ℕ)*((4*(levelRho n)^8/(levelRho n)+1/(n:ℝ))/(levelRho n)^4)+
        (m+1)*(2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)+1/(n:ℝ))^(greedyBlockCount B t n)<1) :
    continuousMixedMass β J (timeScale n)≤bankEndpointError n ∧
      discreteMixedMass β J ⌊timeScale n⌋₊≤bankEndpointError n := by
  let p := B*greedyBlockCount B t n
  let K : Fin p → ℕ := scheduledBankSize c B n
  let a : Fin p → ℝ := fun j => Real.exp (-c (j.val%B)*levelLogScale n)
  let δ : Fin p → ℝ := fun j => Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n)
  let S := lockingUnion n μ t (levelRho n) q b b'
  have hK : ∀j,0<K j := scheduledBankSize_pos c B n
  obtain ⟨z,hz,hzmass⟩ := exists_fixed_good_bank β J K (blockPrior p B) (blockPrior_not_self p B) t q a δ
    (fun j => (Real.exp_pos _).le) S (fun j w => hcov (j.val%B) (Nat.mod_lt _ hB) (fun x => ∀i,|overlap (w i) x|≤3*t))
    (3*Real.exp (-4*levelLogScale n))
    (scheduled_bank_total hB c hc hL hp hdom (replicaGibbsMass_nonneg β J S) hv) hsmall
  let v := initialBankReference (natBankPool K z) (natBankDefault K hK z) B t q
  have HC : ∀m≤⌈Real.exp (2*levelLogScale n)⌉₊,
      (∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) m x)≤9*Real.exp (-2*levelLogScale n) := by
    intro m hm
    have HM := bank_stationary_crossing hn β J μ B H (greedyBlockCount B t n) m t (levelRho n) b b' q G (by simpa only [Nat.cast_mul] using hcount m hm) K hK z hz
    have HK : (m:ℝ)+1≤3*Real.exp (2*levelLogScale n) := by
      have hi : (m:ℝ)≤(⌈Real.exp (2*levelLogScale n)⌉₊:ℝ) := by exact_mod_cast hm
      exact (add_le_add hi (le_refl (1:ℝ))).trans (horizon_size_bound (by linarith only [hL]))
    change _≤((m:ℝ)+1)*(gibbsFiniteLaw β J).prob (fun x => bankCoverageBad K (blockPrior p B) t q z x ∨ bankVertexBad (fun i : BankIndex K => i.1.val) S z x) at HM
    refine HM.trans ?_
    calc
      _ ≤ (3*Real.exp (2*levelLogScale n))*(3*Real.exp (-4*levelLogScale n)) :=
        mul_le_mul HK hzmass ((gibbsFiniteLaw β J).prob_nonneg _) (by positivity)
      _ = _ := by rw [mul_mul_mul_comm,← Real.exp_add]; norm_num; ring
  have HH := mixedMass_bounds_of_crossing hn β J (levelLogScale n) (9*Real.exp (-2*levelLogScale n)) (by linarith only [hL]) (by positivity) v HC
  refine ⟨HH.1,HH.2.trans ?_⟩
  dsimp only [bankEndpointError]
  have hp0 : 0≤(n:ℝ)*Real.exp (-levelLogScale n) := by positivity
  linarith only [hp0]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_IdentityMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem site_clock_tail_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-levelLogScale n)) atTop (𝓝 0) := by
  simpa only [pow_one,neg_one_mul,levelLogScale] using
    polynomial_rpow_exp_decay (by norm_num [kappa] : 0<kappa) zero_lt_one 1

 theorem bankEndpointError_nonneg (n : ℕ) : 0≤bankEndpointError n := by
  unfold bankEndpointError
  positivity

 theorem bankEndpointError_tendsto : Tendsto bankEndpointError atTop (𝓝 0) := by
  have H := (((stretched_exp_decay (by norm_num : (0:ℝ)<2)).const_mul 9).add site_clock_tail_tendsto).const_mul 4
  change Tendsto (fun n => 4*(9*Real.exp (-2*levelLogScale n)+(n:ℝ)*Real.exp (-levelLogScale n))) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using H

 theorem identity_main_of_static_locking_oai (β : ℝ) (μ : ProbabilityMeasure ℝ) {t b b' q : ℝ}
    (ht : 0<t) (hb : 0<b) (hpack : 3*t<b^2/2) (hcut : 3*t<b) (hcut' : 2*t<b') (hh : 2*t<q)
    (hcov : ∀D : ℝ,0<D → ∃c : ℝ,0 < c ∧ ∃C : (n : ℕ) → Set (Disorder n),
      (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
      ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
        finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*levelLogScale n)))<Real.exp (-D*levelLogScale n))
    (hstatic : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b') ∂disorderLaw n)≤3*Real.exp (-(n:ℝ)^((4:ℝ)/5))) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  let H : ℕ := ⌈2/b^2⌉₊
  let B : ℕ := H+1
  have hB : 0<B := Nat.succ_pos H
  obtain ⟨c,hc,C,hC,hC1,hcovC⟩ := exists_coverage_schedule β q hcov
  let A := 3*bankPrefix c B+20
  let V (n : ℕ) : Set (Disorder n) := {J | replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b')≤Real.exp (-A*levelLogScale n)}
  let D (n : ℕ) : Set (Disorder n) := finiteGoodEvent C B n ∩ V n
  have hV (n : ℕ) : MeasurableSet (V n) := measurableSet_le (continuous_replicaGibbsMass β _).measurable measurable_const
  have hV1 : Tendsto (fun n => (disorderLaw n).real (V n)) atTop (𝓝 1) :=
    high_probability_small_replica β _ (by norm_num [kappa] : kappa<(4:ℝ)/5) 3 A hstatic
  have hD (n : ℕ) : MeasurableSet (D n) := (finiteGoodEvent_measurable C hC B n).inter (hV n)
  have hD1 : Tendsto (fun n => (disorderLaw n).real (D n)) atTop (𝓝 1) :=
    high_probability_inter _ _ hV (finiteGoodEvent_tendsto C hC hC1 B) hV1
  apply main_of_quenched_mixed_bounds β D hD hD1 bankEndpointError bankEndpointError_nonneg bankEndpointError_tendsto
  have hsmall : Tendsto (fun n => 3*Real.exp (-4*levelLogScale n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (stretched_exp_decay (by norm_num : (0:ℝ)<4)).const_mul 3
  filter_upwards [eventually_gt_atTop (0:ℕ),stretchedLogScale_tendsto.eventually_ge_atTop 5,
    eventually_exp_dominates_linear (bankPrefix c B+5),eventually_exp_dominates_linear (t/8),
    hsmall.eventually_lt_const zero_lt_one,
    greedyScale_eventual hB (show H<B by omega) ht hb le_rfl hpack hcut hcut' hh,
    greedy_count_eventual hB ht] with n hn hL hdom hp hsmalln G hcount
  intro J hJ
  have hcovJ (j : ℕ) (hj : j<B) := hcovC j n J ((finiteGoodEvent_mem C B n J).mp hJ.1 j hj)
  exact identity_quenched_bound hn hB β J μ t b b' q c (fun j => (hc j).le) hcovJ hJ.2 hL
    ((greedy_level_count_bound hB ht n).trans hp) hdom hsmalln G hcount

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.identity_main_of_static_locking_oai := @OAI.SK.Analytic.identity_main_of_static_locking_oai
