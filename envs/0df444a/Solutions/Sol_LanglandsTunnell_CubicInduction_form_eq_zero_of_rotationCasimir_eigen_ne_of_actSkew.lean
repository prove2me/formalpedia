-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.form_eq_zero_of_rotationCasimir_eigen_ne_of_actSkew
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ae94ca5e-30cc-5726-a99d-5eb3a8abd769

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_form_eq_zero_of_rotationCasimir_eigen_ne_of_actSkew

set_option autoImplicit false

namespace WsC
namespace O3a

open MvPolynomial

noncomputable section

abbrev R9 := MvPolynomial (Fin 3 × Fin 3) ℂ

def orth (o : Fin 3 → Fin 3 → ℝ) : Prop := ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0

def co (o : Fin 3 → Fin 3 → ℝ) : Fin 3 × Fin 3 → ℂ := fun ij => ((o ij.1 ij.2 : ℝ) : ℂ)

theorem abstract (W : Submodule ℂ R9) (β : R9 → R9 → ℂ) (κ κ' : ℂ) (hκ : κ ≠ κ')
    (P Q : R9) (hP : P ∈ W) (hQ : Q ∈ W)
    (A : Fin 3 → Fin 3 → R9 → R9)
    (hstab : ∀ P ∈ W, ∀ c d : Fin 3, A c d P ∈ W)
    (hlin : ∀ (z : ℂ), ∀ P₁ ∈ W, ∀ P₂ ∈ W, ∀ Q ∈ W, β (z • P₁ + P₂) Q = z * β P₁ Q + β P₂ Q)
    (hherm : ∀ P ∈ W, ∀ Q ∈ W, β Q P = (starRingEnd ℂ) (β P Q))
    (hnull : ∀ P ∈ W, (∀ o : Fin 3 → Fin 3 → ℝ, orth o → eval (co o) P = 0) → ∀ Q ∈ W, β P Q = 0)
    (hposv : ∀ P ∈ W, (∃ o : Fin 3 → Fin 3 → ℝ, orth o ∧ eval (co o) P ≠ 0) → 0 < (β P P).re)
    (hskew : ∀ P ∈ W, ∀ Q ∈ W, ∀ c d : Fin 3, β (A c d P) Q = -β P (A c d Q))
    (Ω : R9 → R9)
    (hΩ : ∀ R, Ω R = (A 0 1 (A 0 1 R - A 1 0 R) - A 1 0 (A 0 1 R - A 1 0 R)) +
        (A 0 2 (A 0 2 R - A 2 0 R) - A 2 0 (A 0 2 R - A 2 0 R)) +
        (A 1 2 (A 1 2 R - A 2 1 R) - A 2 1 (A 1 2 R - A 2 1 R)))
    (hPe : ∀ o : Fin 3 → Fin 3 → ℝ, orth o → eval (co o) (Ω P) = κ * eval (co o) P)
    (hQe : ∀ o : Fin 3 → Fin 3 → ℝ, orth o → eval (co o) (Ω Q) = κ' * eval (co o) Q) :
    β P Q = 0 := by

  have h0W : (0 : R9) ∈ W := W.zero_mem
  have hzero : ∀ R ∈ W, β 0 R = 0 := by
    intro R hR
    have h := hlin 1 0 h0W 0 h0W R hR
    rw [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have hsmul : ∀ (z : ℂ), ∀ R ∈ W, ∀ S ∈ W, β (z • R) S = z * β R S := by
    intro z R hR S hS
    have h := hlin z R hR 0 h0W S hS
    rwa [add_zero, hzero S hS, add_zero] at h
  have hadd : ∀ R₁ ∈ W, ∀ R₂ ∈ W, ∀ S ∈ W, β (R₁ + R₂) S = β R₁ S + β R₂ S := by
    intro R₁ h₁ R₂ h₂ S hS
    have h := hlin 1 R₁ h₁ R₂ h₂ S hS
    rwa [one_smul, one_mul] at h
  have hsub : ∀ R₁ ∈ W, ∀ R₂ ∈ W, ∀ S ∈ W, β (R₁ - R₂) S = β R₁ S - β R₂ S := by
    intro R₁ h₁ R₂ h₂ S hS
    have h := hlin (-1) R₂ h₂ R₁ h₁ S hS
    rw [show (-1 : ℂ) • R₂ + R₁ = R₁ - R₂ by
      rw [neg_one_smul, add_comm, sub_eq_add_neg]] at h
    rw [h]; ring

  have hsub' : ∀ R ∈ W, ∀ S₁ ∈ W, ∀ S₂ ∈ W, β R (S₁ - S₂) = β R S₁ - β R S₂ := by
    intro R hR S₁ h₁ S₂ h₂
    rw [hherm _ (W.sub_mem h₁ h₂) _ hR, hsub S₁ h₁ S₂ h₂ R hR, map_sub, ← hherm _ h₁ _ hR,
      ← hherm _ h₂ _ hR]
  have hadd' : ∀ R ∈ W, ∀ S₁ ∈ W, ∀ S₂ ∈ W, β R (S₁ + S₂) = β R S₁ + β R S₂ := by
    intro R hR S₁ h₁ S₂ h₂
    rw [hherm _ (W.add_mem h₁ h₂) _ hR, hadd S₁ h₁ S₂ h₂ R hR, map_add, ← hherm _ h₁ _ hR,
      ← hherm _ h₂ _ hR]

  set L : Fin 3 → Fin 3 → R9 → R9 := fun a b R => A a b R - A b a R with hL
  have hLW : ∀ a b, ∀ R ∈ W, L a b R ∈ W := fun a b R hR => W.sub_mem (hstab R hR a b) (hstab R hR b a)
  have hLskew : ∀ a b, ∀ R ∈ W, ∀ S ∈ W, β (L a b R) S = -β R (L a b S) := by
    intro a b R hR S hS
    simp only [hL]
    rw [hsub _ (hstab R hR a b) _ (hstab R hR b a) S hS, hskew R hR S hS, hskew R hR S hS,
      hsub' R hR _ (hstab S hS a b) _ (hstab S hS b a)]
    ring
  have hLL : ∀ a b, ∀ R ∈ W, ∀ S ∈ W, β (L a b (L a b R)) S = β R (L a b (L a b S)) := by
    intro a b R hR S hS
    rw [hLskew a b _ (hLW a b R hR) S hS, hLskew a b R hR _ (hLW a b S hS), neg_neg]
  have hΩL : ∀ R, Ω R = L 0 1 (L 0 1 R) + L 0 2 (L 0 2 R) + L 1 2 (L 1 2 R) := by
    intro R; rw [hΩ R]
  have hΩW : ∀ R ∈ W, Ω R ∈ W := by
    intro R hR
    rw [hΩL]
    exact W.add_mem (W.add_mem (hLW _ _ _ (hLW _ _ R hR)) (hLW _ _ _ (hLW _ _ R hR)))
      (hLW _ _ _ (hLW _ _ R hR))

  have hΩsa : β (Ω P) Q = β P (Ω Q) := by
    rw [hΩL, hΩL, hadd _ (W.add_mem (hLW _ _ _ (hLW _ _ P hP)) (hLW _ _ _ (hLW _ _ P hP))) _
      (hLW _ _ _ (hLW _ _ P hP)) Q hQ,
      hadd _ (hLW _ _ _ (hLW _ _ P hP)) _ (hLW _ _ _ (hLW _ _ P hP)) Q hQ,
      hadd' P hP _ (W.add_mem (hLW _ _ _ (hLW _ _ Q hQ)) (hLW _ _ _ (hLW _ _ Q hQ))) _
      (hLW _ _ _ (hLW _ _ Q hQ)),
      hadd' P hP _ (hLW _ _ _ (hLW _ _ Q hQ)) _ (hLW _ _ _ (hLW _ _ Q hQ)),
      hLL 0 1 P hP Q hQ, hLL 0 2 P hP Q hQ, hLL 1 2 P hP Q hQ]

  have hreal : ∀ R ∈ W, (starRingEnd ℂ) (β R R) = β R R := fun R hR => (hherm R hR R hR).symm
  have hΩQQ : (starRingEnd ℂ) (β (Ω Q) Q) = β (Ω Q) Q := by
    have h1 : β (Ω Q) Q = -(β (L 0 1 Q) (L 0 1 Q) + β (L 0 2 Q) (L 0 2 Q) + β (L 1 2 Q) (L 1 2 Q)) := by
      rw [hΩL, hadd _ (W.add_mem (hLW _ _ _ (hLW _ _ Q hQ)) (hLW _ _ _ (hLW _ _ Q hQ))) _
        (hLW _ _ _ (hLW _ _ Q hQ)) Q hQ,
        hadd _ (hLW _ _ _ (hLW _ _ Q hQ)) _ (hLW _ _ _ (hLW _ _ Q hQ)) Q hQ,
        hLskew 0 1 _ (hLW _ _ Q hQ) Q hQ, hLskew 0 2 _ (hLW _ _ Q hQ) Q hQ,
        hLskew 1 2 _ (hLW _ _ Q hQ) Q hQ]
      ring
    rw [h1, map_neg, map_add, map_add, hreal _ (hLW _ _ Q hQ), hreal _ (hLW _ _ Q hQ),
      hreal _ (hLW _ _ Q hQ)]

  have hΩP : ∀ R ∈ W, β (Ω P) R = κ * β P R := by
    intro R hR
    have hmem : Ω P - κ • P ∈ W := W.sub_mem (hΩW P hP) (W.smul_mem κ hP)
    have hz : ∀ o : Fin 3 → Fin 3 → ℝ, orth o → eval (co o) (Ω P - κ • P) = 0 := by
      intro o ho; rw [map_sub, smul_eval, hPe o ho, sub_self]
    have h := hnull _ hmem hz R hR
    rw [hsub _ (hΩW P hP) _ (W.smul_mem κ hP) R hR, hsmul κ P hP R hR] at h
    linear_combination h
  have hΩQ : ∀ R ∈ W, β (Ω Q) R = κ' * β Q R := by
    intro R hR
    have hmem : Ω Q - κ' • Q ∈ W := W.sub_mem (hΩW Q hQ) (W.smul_mem κ' hQ)
    have hz : ∀ o : Fin 3 → Fin 3 → ℝ, orth o → eval (co o) (Ω Q - κ' • Q) = 0 := by
      intro o ho; rw [map_sub, smul_eval, hQe o ho, sub_self]
    have h := hnull _ hmem hz R hR
    rw [hsub _ (hΩW Q hQ) _ (W.smul_mem κ' hQ) R hR, hsmul κ' Q hQ R hR] at h
    linear_combination h

  have hmain : κ * β P Q = (starRingEnd ℂ) κ' * β P Q := by
    rw [← hΩP Q hQ, hΩsa, hherm _ (hΩW Q hQ) _ hP, hΩQ P hP, map_mul, ← hherm _ hQ _ hP]
  by_cases hQQ : β Q Q = 0
  ·
    have hvan : ∀ o : Fin 3 → Fin 3 → ℝ, orth o → eval (co o) Q = 0 := by
      intro o ho
      by_contra hne
      have := hposv Q hQ ⟨o, ho, hne⟩
      rw [hQQ] at this
      simp at this
    rw [hherm Q hQ P hP, hnull Q hQ hvan P hP, map_zero]
  ·
    have hκ' : (starRingEnd ℂ) κ' = κ' := by
      have h := hΩQQ
      rw [hΩQ Q hQ, map_mul, hreal Q hQ] at h
      exact mul_right_cancel₀ hQQ h
    rw [hκ'] at hmain
    have : (κ - κ') * β P Q = 0 := by rw [sub_mul, hmain, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hκ)

theorem main
    (ν : Fin 3 → ℂ) (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ))
    (β : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ → ℂ) (κ κ' : ℂ) (hκ : κ ≠ κ')
    (P Q : MvPolynomial (Fin 3 × Fin 3) ℂ) (hP : P ∈ W) (hQ : Q ∈ W) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let Ω : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun P => (act ν 0 1 (act ν 0 1 P - act ν 1 0 P) - act ν 1 0 (act ν 0 1 P - act ν 1 0 P)) +
        (act ν 0 2 (act ν 0 2 P - act ν 2 0 P) - act ν 2 0 (act ν 0 2 P - act ν 2 0 P)) +
        (act ν 1 2 (act ν 1 2 P - act ν 2 1 P) - act ν 2 1 (act ν 1 2 P - act ν 2 1 P))
    (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) →
    (∀ (z : ℂ), ∀ P₁ ∈ W, ∀ P₂ ∈ W, ∀ Q ∈ W, β (z • P₁ + P₂) Q = z * β P₁ Q + β P₂ Q) →
    (∀ P ∈ W, ∀ Q ∈ W, β Q P = (starRingEnd ℂ) (β P Q)) →
    (∀ P ∈ W, (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0) → ∀ Q ∈ W, β P Q = 0) →
    (∀ P ∈ W, (∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) → 0 < (β P P).re) →
    (∀ P ∈ W, ∀ Q ∈ W, ∀ c d : Fin 3, β (act ν c d P) Q = -β P (act ν c d Q)) →
    (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (Ω P) = κ * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P) →
    (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (Ω Q) = κ' * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q) →
    β P Q = 0 := by
  intro act Ω hstab hlin hherm hnull hposv hskew hPe hQe
  exact abstract W β κ κ' hκ P Q hP hQ (act ν) hstab hlin hherm hnull hposv hskew Ω
    (fun R => rfl) hPe hQe

end

end WsC.O3a

theorem solution
    (ν : Fin 3 → ℂ) (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ))
    (β : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ → ℂ) (κ κ' : ℂ) (hκ : κ ≠ κ')
    (P Q : MvPolynomial (Fin 3 × Fin 3) ℂ) (hP : P ∈ W) (hQ : Q ∈ W) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let Ω : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun P => (act ν 0 1 (act ν 0 1 P - act ν 1 0 P) - act ν 1 0 (act ν 0 1 P - act ν 1 0 P)) +
        (act ν 0 2 (act ν 0 2 P - act ν 2 0 P) - act ν 2 0 (act ν 0 2 P - act ν 2 0 P)) +
        (act ν 1 2 (act ν 1 2 P - act ν 2 1 P) - act ν 2 1 (act ν 1 2 P - act ν 2 1 P))
    (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) →
    (∀ (z : ℂ), ∀ P₁ ∈ W, ∀ P₂ ∈ W, ∀ Q ∈ W, β (z • P₁ + P₂) Q = z * β P₁ Q + β P₂ Q) →
    (∀ P ∈ W, ∀ Q ∈ W, β Q P = (starRingEnd ℂ) (β P Q)) →
    (∀ P ∈ W, (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0) → ∀ Q ∈ W, β P Q = 0) →
    (∀ P ∈ W, (∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) → 0 < (β P P).re) →
    (∀ P ∈ W, ∀ Q ∈ W, ∀ c d : Fin 3, β (act ν c d P) Q = -β P (act ν c d Q)) →
    (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (Ω P) = κ * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P) →
    (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (Ω Q) = κ' * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q) →
    β P Q = 0 := by
  exact WsC.O3a.main ν W β κ κ' hκ P Q hP hQ

end S_LanglandsTunnell_CubicInduction_form_eq_zero_of_rotationCasimir_eigen_ne_of_actSkew
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_form_eq_zero_of_rotationCasimir_eigen_ne_of_actSkew (solution)
