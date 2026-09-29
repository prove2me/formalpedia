-- Prove2me | solution 1 for MTT.ordinary_root_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-05T22:27:55.626738+00:00
-- url     : https://prove2.me/submissions/94bc7430-5043-478a-ac90-eb6a3c6f3939

import Definitions.Def_MTT_Measures
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
noncomputable section

private lemma unit_root {K : Type*} [NormedField K] [IsAlgClosed K]
    [IsUltrametricDist K] [CharZero K] (a b : K) (ha : ‖a‖ = 1) (hb : ‖b‖ < 1) :
    ∃! x : K, ‖x‖ = 1 ∧ x^2 - a*x + b = 0 := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (a^2 - 4*b) (by decide : 0 < 2)
  let x := (a+d)/2
  let y := (a-d)/2
  have hs : x+y=a := by dsimp [x,y]; ring
  have hp : x*y=b := by dsimp [x,y]; linear_combination -hd / 4
  have hnorm : ‖x‖ * ‖y‖ < 1 := by rw [← norm_mul, hp]; exact hb
  have hmax : 1 ≤ max ‖x‖ ‖y‖ := by
    rw [← ha, ← hs]; exact IsUltrametricDist.norm_add_le_max x y
  have choose_root : ∀ u v : K, u+v=a → u*v=b → ‖u‖ < 1 →
      ∃! z : K, ‖z‖ = 1 ∧ z^2-a*z+b=0 := by
    intro u v huv huv' hu
    have hvle : ‖v‖ ≤ 1 := by
      have h := IsUltrametricDist.norm_add_le_max a (-u)
      have hv : a-u=v := by rw [← huv]; ring
      simp only [← sub_eq_add_neg, norm_neg] at h
      rw [hv, ha, max_eq_left hu.le] at h
      exact h
    have hvge : 1 ≤ ‖v‖ := by
      have h := IsUltrametricDist.norm_add_le_max u v
      rw [huv, ha] at h
      rcases le_max_iff.mp h with h | h
      · linarith
      · exact h
    have hv : ‖v‖ = 1 := le_antisymm hvle hvge
    refine ⟨v, ⟨hv, ?_⟩, ?_⟩
    · rw [← huv, ← huv']; ring
    · intro z hz
      have hf : (z-u)*(z-v)=0 := by
        calc
          (z-u)*(z-v) = z^2-(u+v)*z+u*v := by ring
          _ = 0 := by rw [huv, huv']; exact hz.2
      rcases mul_eq_zero.mp hf with h | h
      · have he := sub_eq_zero.mp h
        rw [he] at hz
        linarith [hz.1]
      · exact sub_eq_zero.mp h
  by_cases hx : ‖x‖ < 1
  · exact choose_root x y hs hp hx
  · have hy : ‖y‖ < 1 := by
      have hn := norm_nonneg y
      nlinarith
    exact choose_root y x (by rw [add_comm]; exact hs) (by rw [mul_comm]; exact hp) hy

open MTT in
theorem solution
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (hord : ‖ιp (f.coeff p)‖ = 1) :
    ∃! α : ℂ_[p], IsOrdinaryRoot f ιp α := by
  have he : ‖ιp (f.epsilon p)‖ ≤ 1 := by
    exact DirichletCharacter.norm_le_one (f.epsilon.ringHomComp ιp) p
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    have h := norm_algebraMap' ℂ_[p] (p : ℚ_[p])
    simp only [map_natCast] at h
    rw [h]
    exact Padic.norm_p_lt_one
  have hb : ‖ιp (f.epsilon p) * (p : ℂ_[p])^(k-1)‖ < 1 := by
    rw [norm_mul, norm_pow]
    have ht : ‖(p : ℂ_[p])‖^(k-1) < 1 := pow_lt_one₀ (norm_nonneg _) hp (by omega)
    exact lt_of_le_of_lt (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) he) ht
  exact unit_root _ _ hord hb
