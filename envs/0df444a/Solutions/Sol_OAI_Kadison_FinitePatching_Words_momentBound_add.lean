-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.Words.momentBound_add
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:40:25.559461+00:00
-- url     : https://prove2.me/submissions/fa2d11fe-1848-443b-8714-87033e7a05e0

import Mathlib
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C035
import Theorems.Thm_OAI_Kadison_FinitePatching_Words_word_perturbation_bound

section
-- module Solutions.OAIQ039_CM.Commutator_ExponentialMomentBudget
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FinitePatching

lemma budgetSlope_ge_one (N : ℕ) {η : ℝ} (hη : 0<η) : 1 ≤ budgetSlope N η := by
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hd : 0 ≤ 2/η := by positivity
  have h1 : 1 ≤ ((N:ℝ)+1)^2 := by nlinarith
  exact (one_mul (1:ℝ)).symm ▸ mul_le_mul h1 (by linarith : 1 ≤ 1+2/η)
    (by norm_num) (by positivity)

lemma momentBudget_nonneg {ε : ℝ} (hε : 0 ≤ ε) (K t : ℝ) : 0 ≤ momentBudget ε K t :=
  mul_nonneg hε (Real.exp_pos _).le

lemma le_momentBudget {ε K t : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) (ht : 0 ≤ t) :
    ε ≤ momentBudget ε K t := by
  exact le_mul_of_one_le_right hε (Real.one_le_exp (mul_nonneg hK ht))

lemma momentBudget_step {ε K t q : ℝ} (hε : 0 ≤ ε) :
    momentBudget ε K t+K*momentBudget ε K t*q ≤ momentBudget ε K (t+q) := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (K*q))
    (momentBudget_nonneg hε K t)
  calc
    _=momentBudget ε K t*(K*q+1) := by ring
    _ ≤ momentBudget ε K t*Real.exp (K*q) := hh
    _=momentBudget ε K (t+q) := by simp only [momentBudget,mul_add,Real.exp_add,mul_assoc]

lemma word_momentBudget_step {ε η t q : ℝ} (hε : 0 ≤ ε) (hη : 0<η)
    (ht : 0 ≤ t) (hq : 0 ≤ q) {n N : ℕ} (hn : n ≤ N) :
    momentBudget ε (budgetSlope N η) t+
      ((n:ℝ)+(n:ℝ)^2)*(ε+2*momentBudget ε (budgetSlope N η) t/η)*q ≤
      momentBudget ε (budgetSlope N η) (t+q) := by
  let B := momentBudget ε (budgetSlope N η) t
  have hB : 0 ≤ B := momentBudget_nonneg hε _ _
  have hK : 0 ≤ budgetSlope N η := (by norm_num : (0:ℝ) ≤ 1).trans (budgetSlope_ge_one N hη)
  have hεB : ε ≤ B := le_momentBudget hε hK ht
  have hn' : (n:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr hn
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hf : (n:ℝ)+(n:ℝ)^2 ≤ ((N:ℝ)+1)^2 := by nlinarith
  have hd : ε+2*B/η ≤ (1+2/η)*B := by
    calc
      _ ≤ B+2*B/η := add_le_add hεB le_rfl
      _=_ := by ring
  have hh : ((n:ℝ)+(n:ℝ)^2)*(ε+2*B/η) ≤ budgetSlope N η*B := by
    calc
      _ ≤ ((N:ℝ)+1)^2*((1+2/η)*B) := mul_le_mul hf hd (by positivity) (by positivity)
      _=_ := by dsimp [budgetSlope]; ring
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hq)).trans (momentBudget_step hε)

lemma pure_momentBudget_step {ε η t q : ℝ} (hε : 0 ≤ ε) (hη : 0<η)
    (ht : 0 ≤ t) (hq : 0 ≤ q) (N : ℕ) :
    momentBudget ε (budgetSlope N η) t+ε*q ≤ momentBudget ε (budgetSlope N η) (t+q) := by
  have hK := budgetSlope_ge_one N hη
  have hB := momentBudget_nonneg hε (budgetSlope N η) t
  have hεB := le_momentBudget hε ((by norm_num : (0:ℝ) ≤ 1).trans hK) ht
  have hh : ε ≤ budgetSlope N η*momentBudget ε (budgetSlope N η) t :=
    hεB.trans (le_mul_of_one_le_left hB hK)
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hq)).trans (momentBudget_step hε)

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable (A : Type*) [CStarAlgebra A]

namespace PartialUnitary

variable {A}

lemma val_mul_zero {v w : PartialUnitary A} (h : v.support*w.support=0) : v.val*w.val=0 :=
  by simpa [power] using power_mul_power_zero h 1 1

lemma pow_add_of_mul_zero {a b : A} (hab : a*b=0) (hba : b*a=0) (n : ℕ) :
    (a+b)^(n+1)=a^(n+1)+b^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a^(n+1)*b=0 := by rw [pow_succ,mul_assoc,hab,mul_zero]
    have h2 : b^(n+1)*a=0 := by rw [pow_succ,mul_assoc,hba,mul_zero]
    rw [pow_succ,ih,add_mul,mul_add,mul_add,h1,h2]
    simp only [add_zero,zero_add,←pow_succ]

lemma add_power (v w : PartialUnitary A) (h : v.support*w.support=0) (k : ℤ) :
    (v.add w h).power k=v.power k+w.power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      exact pow_add_of_mul_zero (val_mul_zero h) (val_mul_zero (orthogonal_support_symm h)) n
  | negSucc n =>
    change (star (v.val+w.val))^(n+1)=(star v.val)^(n+1)+(star w.val)^(n+1)
    rw [star_add]
    apply pow_add_of_mul_zero
    · simpa only [StarMul.star_mul,star_zero] using congrArg star (val_mul_zero (orthogonal_support_symm h))
    · simpa only [StarMul.star_mul,star_zero] using congrArg star (val_mul_zero h)

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialMomentBudget
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

include hτ in
theorem momentBound_add_oai (hx : ∀ j,‖x j‖ ≤ 1)
    (v w : PartialUnitary A) (horth : v.support*w.support=0)
    (hqp : w.support ≤ 1-v.support) {N : ℕ} {ε η : ℝ}
    (hε : 0 ≤ ε) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
    (hbound : MomentBound τ x k v N (momentBudget ε (budgetSlope N η) (τ v.support).re))
    (hpure : ∀ i,‖τ (w.power (k i))‖ ≤ ε*(τ w.support).re)
    (hsmall : ∀ (s : List (Letter J K)) (j : J),s.length ≤ N →
      TracialL2.norm τ (w.support*cornerCenter τ (1-v.support) (word x k v s*x j)*w.support)^2 ≤
        ε^2*(τ w.support).re)
    (hphase : ∀ (s t : List (Letter J K)) (j : J) (i : K),s.length ≤ N → t.length ≤ N →
      ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ ε*(τ w.support).re) :
    MomentBound τ x k (v.add w horth) N
      (momentBudget ε (budgetSlope N η) (τ (v.add w horth).support).re) := by
  have ht : 0 ≤ (τ v.support).re := (τ.map_nonneg v.projection.nonneg).1
  have hq : 0 ≤ (τ w.support).re := (τ.map_nonneg w.projection.nonneg).1
  have he : (τ (v.add w horth).support).re=(τ v.support).re+(τ w.support).re := by
    change (τ (v.support+w.support)).re=_
    rw [map_add,Complex.add_re]
  constructor
  · intro i
    rw [v.add_power w horth,map_add]
    exact (norm_add_le _ _).trans ((add_le_add (hbound.1 i) (hpure i)).trans
      (by rw [he]; exact pure_momentBudget_step hε hη ht hq N))
  · intro l hl hlen hv
    have hh := word_perturbation_bound τ hτ x k hx v w horth hqp
      (momentBudget_nonneg hε _ _) hε hη hrest hbound hsmall hphase l hlen hv
    calc
      _ ≤ ‖τ (word x k v l)‖+‖τ (word x k (v.add w horth) l)-τ (word x k v l)‖ := by
        simpa only [norm_sub_rev] using norm_le_insert (τ (word x k v l))
          (τ (word x k (v.add w horth) l))
      _ ≤ momentBudget ε (budgetSlope N η) (τ v.support).re+
          ((l.length:ℝ)+(l.length:ℝ)^2)*
            (ε+2*momentBudget ε (budgetSlope N η) (τ v.support).re/η)*(τ w.support).re :=
        add_le_add (hbound.2 l hl hlen hv) hh
      _ ≤ _ := by rw [he]; exact word_momentBudget_step hε hη ht hq hlen

end Kadison.FinitePatching.Words

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.FinitePatching.Words.momentBound_add_oai.{u_1, u_2, u_3} := @OAI.Kadison.FinitePatching.Words.momentBound_add_oai.{u_1, u_2, u_3}
