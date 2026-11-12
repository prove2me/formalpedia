-- Prove2me | solution 1 for HolonomicPositivity.Robust.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:43:03.017237+00:00
-- url     : https://prove2.me/submissions/230d9713-d2cc-4617-b97b-18bac82603bd

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Comparison
import Definitions.Def_HolonomicPositivity_Robust_Conditions
import Theorems.Thm_HolonomicPositivity_Robust_lemma_5_3
import Theorems.Thm_HolonomicPositivity_Robust_lemma_5_4_scaling_case_II_1
import Theorems.Thm_HolonomicPositivity_Robust_lemma_5_4_scaling_case_II_2
import Theorems.Thm_HolonomicPositivity_Robust_lemma_5_4_scaling_case_II_3

section
set_option autoImplicit false
open Filter Topology Asymptotics

namespace HolonomicPositivity.Dev.RatExp
open HolonomicPositivity.Robust

lemma ev_eq (U : RatFunc ℝ) (x : ℝ) : ev U x = U.num.eval x / U.denom.eval x := by
  simp [ev, RatFunc.eval, Polynomial.eval₂_id]

lemma eventually_denom_ne (U : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop, U.denom.eval x ≠ 0 := by
  filter_upwards [Polynomial.eventually_atTop_not_isRoot U.denom U.denom_ne_zero] with x hx
  exact hx

lemma eventually_ev_ne (U : RatFunc ℝ) (hU : U ≠ 0) : ∀ᶠ x : ℝ in atTop, ev U x ≠ 0 := by
  filter_upwards [Polynomial.eventually_atTop_not_isRoot U.denom U.denom_ne_zero,
    Polynomial.eventually_atTop_not_isRoot U.num (RatFunc.num_ne_zero hU)] with x h1 h2
  rw [ev_eq]
  exact div_ne_zero h2 h1

lemma ev_add (U V : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop, ev (U + V) x = ev U x + ev V x := by
  filter_upwards [eventually_denom_ne U, eventually_denom_ne V] with x hU hV
  exact RatFunc.eval_add _ _ (by simpa using hU) (by simpa using hV)

lemma ev_mul (U V : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop, ev (U * V) x = ev U x * ev V x := by
  filter_upwards [eventually_denom_ne U, eventually_denom_ne V] with x hU hV
  exact RatFunc.eval_mul _ _ (by simpa using hU) (by simpa using hV)

lemma ev_inv (U : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop, ev U⁻¹ x = (ev U x)⁻¹ := by
  by_cases hU : U = 0
  · subst hU; simp [ev]
  · filter_upwards [ev_mul U U⁻¹, eventually_ev_ne U hU] with x h1 h2
    rw [mul_inv_cancel₀ hU] at h1
    have : ev (1 : RatFunc ℝ) x = 1 := by simp [ev]
    rw [this] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm

/-- `f` agrees eventually (at `+∞`) with the evaluation of the rational function `U`. -/
def Rep (f : ℝ → ℝ) (U : RatFunc ℝ) : Prop := ∀ᶠ x : ℝ in atTop, f x = ev U x

lemma Rep.self (U : RatFunc ℝ) : Rep (ev U) U := Eventually.of_forall fun _ => rfl

lemma Rep.add {f g : ℝ → ℝ} {U V : RatFunc ℝ} (hf : Rep f U) (hg : Rep g V) :
    Rep (fun x => f x + g x) (U + V) := by
  filter_upwards [hf, hg, ev_add U V] with x h1 h2 h3
  rw [h3, h1, h2]

lemma Rep.mul {f g : ℝ → ℝ} {U V : RatFunc ℝ} (hf : Rep f U) (hg : Rep g V) :
    Rep (fun x => f x * g x) (U * V) := by
  filter_upwards [hf, hg, ev_mul U V] with x h1 h2 h3
  rw [h3, h1, h2]

lemma Rep.const (c : ℝ) : Rep (fun _ => c) (RatFunc.C c) :=
  Eventually.of_forall fun x => by simp [ev]

lemma Rep.neg {f : ℝ → ℝ} {U : RatFunc ℝ} (hf : Rep f U) :
    Rep (fun x => - f x) (RatFunc.C (-1) * U) := by
  have := (Rep.const (-1)).mul hf
  refine this.mono fun x hx => ?_
  simpa using hx

lemma Rep.sub {f g : ℝ → ℝ} {U V : RatFunc ℝ} (hf : Rep f U) (hg : Rep g V) :
    Rep (fun x => f x - g x) (U + RatFunc.C (-1) * V) := by
  have := hf.add hg.neg
  refine this.mono fun x hx => ?_
  simpa [sub_eq_add_neg] using hx

lemma Rep.congr {f g : ℝ → ℝ} {U : RatFunc ℝ} (hf : Rep f U) (h : ∀ᶠ x : ℝ in atTop, g x = f x) :
    Rep g U := by
  filter_upwards [hf, h] with x h1 h2
  rw [h2, h1]

/-- Shift of a rational function: `(shiftRF c U)(x) = U(x + c)`. -/
noncomputable def shiftRF (c : ℝ) (U : RatFunc ℝ) : RatFunc ℝ :=
  algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.num.comp (Polynomial.X + Polynomial.C c)) /
    algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.denom.comp (Polynomial.X + Polynomial.C c))

lemma ev_alg (p : Polynomial ℝ) (x : ℝ) :
    ev (algebraMap (Polynomial ℝ) (RatFunc ℝ) p) x = p.eval x := by
  simp [ev]

lemma ev_shiftRF (c : ℝ) (U : RatFunc ℝ) : ∀ᶠ x : ℝ in atTop,
    ev (shiftRF c U) x = ev U (x + c) := by
  have h1 := ev_mul (algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.num.comp (Polynomial.X + Polynomial.C c)))
    (algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.denom.comp (Polynomial.X + Polynomial.C c)))⁻¹
  have h2 := ev_inv (algebraMap (Polynomial ℝ) (RatFunc ℝ) (U.denom.comp (Polynomial.X + Polynomial.C c)))
  filter_upwards [h1, h2] with x e1 e2
  unfold shiftRF
  rw [div_eq_mul_inv, e1, e2, ev_alg, ev_alg, ev_eq U (x + c)]
  simp [div_eq_mul_inv]

lemma Rep.shift {f : ℝ → ℝ} {U : RatFunc ℝ} (hf : Rep f U) (c : ℝ) :
    Rep (fun x => f (x + c)) (shiftRF c U) := by
  have h : ∀ᶠ x : ℝ in atTop, f (x + c) = ev U (x + c) :=
    (tendsto_atTop_add_const_right atTop c tendsto_id).eventually hf
  filter_upwards [h, ev_shiftRF c U] with x h1 h2
  rw [h1, h2]


/-! ### Eventual sign of a rational function -/

/-! ### Taylor expansion at infinity -/

end HolonomicPositivity.Dev.RatExp
end

section
set_option autoImplicit false

namespace HolonomicPositivity.Dev.Iface
open HolonomicPositivity.Robust

/-- What a case of Lemma 5.4 must produce: a scaling S satisfying (1), B > 0, inequality (6) for A/(B B(x-1)), and (3). -/
def Goal (P Q : RatFunc ℝ) : Prop :=
  ∃ S : RatFunc ℝ, EventuallyGE (ev S) (fun _ => 0) ∧ EventuallyGT (scaledB S) (fun _ => 0) ∧
    SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧ EventuallyGE (scaledC P Q S) (fun _ => 0)

end HolonomicPositivity.Dev.Iface
end

section
set_option autoImplicit false
open Filter Topology Asymptotics

namespace HolonomicPositivity.Dev.L54
open HolonomicPositivity.Robust HolonomicPositivity.Dev.RatExp

lemma shift_ev {f g : ℝ → ℝ} (h : ∀ᶠ x in atTop, f x = g x) (c : ℝ) :
    ∀ᶠ x in atTop, f (x + c) = g (x + c) :=
  (tendsto_atTop_add_const_right atTop c tendsto_id).eventually h

lemma gt_congr {U U' V V' : ℝ → ℝ} (hU : ∀ᶠ x in atTop, U x = U' x) (hV : ∀ᶠ x in atTop, V x = V' x)
    (h : EventuallyGT U V) : EventuallyGT U' V' := by
  filter_upwards [hU, hV, h] with x a b c
  rw [← a, ← b]; exact c

lemma eqmod_congr {U U' V : ℝ → ℝ} (hU : ∀ᶠ x in atTop, U x = U' x) {v : ℤ}
    (h : EqMod U V v) : EqMod U' V v := by
  unfold EqMod at *
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hU] with x a
  rw [a]

lemma gemod_congr {U U' V : ℝ → ℝ} (hU : ∀ᶠ x in atTop, U x = U' x) {v : ℤ}
    (h : GeMod U V v) : GeMod U' V v := by
  rcases h with h | h
  · exact Or.inl (gt_congr hU (Eventually.of_forall fun _ => rfl) h)
  · exact Or.inr (eqmod_congr hU h)

end HolonomicPositivity.Dev.L54

namespace HolonomicPositivity.Robust
open HolonomicPositivity.Dev.L54 HolonomicPositivity.Dev.RatExp HolonomicPositivity.Dev.Iface

theorem chk_lemma_5_4 (P Q : RatFunc ℝ) (hP : NoPolesOnNat P) (hQ : NoPolesOnNat Q)
    (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (hII : ConditionII P Q) :
    ∃ S : RatFunc ℝ,
      EventuallyGE (ev S) (fun _ => 0) ∧
      (EventuallyGT (scaledB S) (fun _ => 0) ∧
        SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧
        ∃ L : RatFunc ℝ, IsRiccatiWitness (scaledA P S) (scaledB S) L) ∧
      EventuallyGE (scaledC P Q S) (fun _ => 0) := by
  obtain ⟨hge, hlt, p₀, p₁, p₂, p₃, htay, hcase⟩ := hII
  have hG : Goal P Q := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact HolonomicPositivity.Robust.lemma_5_4_scaling_case_II_1 P Q p₀ p₁ p₂ p₃ htay hge hlt h1 h2
    · exact HolonomicPositivity.Robust.lemma_5_4_scaling_case_II_2 P Q p₀ p₁ p₂ p₃ htay hge hlt h1 h2 h3
    · exact HolonomicPositivity.Robust.lemma_5_4_scaling_case_II_3 P Q p₀ p₁ p₂ p₃ htay hge hlt h1 h2 h3
  obtain ⟨S, hS0, hB, h6, hC⟩ := hG
  refine ⟨S, hS0, ⟨hB, h6, ?_⟩, hC⟩
  have rB : Rep (scaledB S) (RatFunc.C 1 + RatFunc.C (-1) * shiftRF 2 (S)) := by
    have := (Rep.const 1).sub (Rep.shift (Rep.self S) 2)
    exact this.congr (Eventually.of_forall fun x => by simp [scaledB])
  set B' : RatFunc ℝ := RatFunc.C 1 + RatFunc.C (-1) * shiftRF 2 S with hB'
  have rA : Rep (scaledA P S) (B' * shiftRF 1 S + P) := by
    have := (rB.mul (Rep.shift (Rep.self S) 1)).add (Rep.self P)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [scaledA]
  set A' : RatFunc ℝ := B' * shiftRF 1 S + P with hA'
  have eB : ∀ᶠ x in atTop, scaledB S x = ev B' x := rB
  have eA : ∀ᶠ x in atTop, scaledA P S x = ev A' x := rA
  have hB2 : EventuallyGT (ev B') (fun _ => 0) :=
    gt_congr eB (Eventually.of_forall fun _ => rfl) hB
  have h6' : SatisfiesInequalitySix (ev A') (ev B') := by
    unfold SatisfiesInequalitySix at *
    refine gemod_congr ?_ h6
    have eB1 := shift_ev eB (-1)
    filter_upwards [eA, eB, eB1] with x a b c
    rw [a, b, show x + -1 = x - 1 from by ring] at *
    rw [c]
  obtain ⟨L, hL⟩ := (lemma_5_3 A' B' hB2).1 h6'
  refine ⟨L, ?_⟩
  obtain ⟨l1, l2, l3⟩ := hL
  refine ⟨l1, ?_, ?_⟩
  · exact gt_congr (Eventually.of_forall fun _ => rfl)
      (Eventually.of_forall fun _ => rfl) (by
        filter_upwards [l2, eB] with x a b
        rw [b]; exact a) |> fun h => h
  · filter_upwards [l3, eA, eB] with x a b c
    rw [b, c]; exact a

end HolonomicPositivity.Robust
end

theorem solution : type_of% @HolonomicPositivity.Robust.chk_lemma_5_4 := @HolonomicPositivity.Robust.chk_lemma_5_4
