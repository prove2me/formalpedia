-- Prove2me | solution 1 for GlobalTheory.Degen.exists_form_limit_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:41:26.780154+00:00
-- url     : https://prove2.me/submissions/a702f812-bf08-412c-aa5b-a5d915fdcddb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFormLimitIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Degen
open MvPolynomial
namespace GlobalTheory.Degen
theorem _root_.solution (R : Type) [CommRing R] (I : Ideal R) (hI : IsAdicComplete I R)
    (σ : Type) [Finite σ] (K : ℕ → Ideal (MvPolynomial σ R)) (t : ℕ)
    (hK : ∀ e F, F.IsHomogeneous t → F ∈ K (e + 1) → F ∈ K e)
    (ha : ∀ e, ∀ a ∈ I ^ (e + 1), MvPolynomial.C a ∈ K e)
    (hs : ∀ e F, F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial σ R, G.IsHomogeneous t ∧
      (∀ d, MvPolynomial.coeff d G ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1))
    (e : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous t) (hFe : F ∈ K e) :
    ∃ F₁ : MvPolynomial σ R, F₁.IsHomogeneous t ∧ (∀ e', F₁ ∈ K e') ∧
      ∀ d, MvPolynomial.coeff d (F - F₁) ∈ I ^ (e + 1) := by
  classical
  have hdesc : ∀ (P : MvPolynomial σ R), P.IsHomogeneous t → ∀ m k, P ∈ K (m + k) → P ∈ K m := by
    intro P hP m k
    induction k with
    | zero => exact id
    | succ k ih => exact fun h => ih (hK _ _ hP h)
  have hcoef : ∀ (j : ℕ) (P : MvPolynomial σ R), (∀ d, coeff d P ∈ I ^ (j + 1)) → P ∈ K j := by
    intro j P hP
    rw [P.as_sum]
    refine Ideal.sum_mem _ fun d _ => ?_
    have : (monomial d (coeff d P) : MvPolynomial σ R) = C (coeff d P) * monomial d 1 := by
      rw [C_mul_monomial, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (ha _ _ (hP d))
  choose G hG1 hG2 hG3 using hs
  let s : (n : ℕ) → {P : MvPolynomial σ R // P.IsHomogeneous t ∧ P ∈ K (e + n)} := fun n =>
    Nat.rec (motive := fun n => {P : MvPolynomial σ R // P.IsHomogeneous t ∧ P ∈ K (e + n)})
      ⟨F, hF, hFe⟩
      (fun n z => ⟨z.1 - G (e + n) z.1 z.2.1 z.2.2, z.2.1.sub (hG1 _ _ _ _), hG3 _ _ _ _⟩) n
  have hs0 : (s 0).1 = F := rfl
  have hsn : ∀ n, (s (n + 1)).1 = (s n).1 - G (e + n) (s n).1 (s n).2.1 (s n).2.2 :=
    fun n => rfl
  have hd : ∀ d m n, m ≤ n → coeff d (s m).1 - coeff d (s n).1 ∈ I ^ (e + m + 1) := by
    intro d m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hsn, coeff_sub, ← sub_add]
      exact Ideal.add_mem _ ih
        (Ideal.pow_le_pow_right (by omega) (hG2 (e + n) (s n).1 (s n).2.1 (s n).2.2 d))
  have hmem : ∀ (n : ℕ) (z : R), z ∈ (I ^ n • ⊤ : Submodule R R) ↔ z ∈ I ^ n := by
    intro n z
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hlim : ∀ d, ∃ L : R, ∀ m, coeff d (s m).1 - L ∈ I ^ (e + m + 1) := by
    intro d
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := R) hI.toIsPrecomplete
      (f := fun n => coeff d (s n).1) (by
        intro m n hmn
        rw [SModEq.sub_mem, hmem]
        exact Ideal.pow_le_pow_right (by omega) (hd d m n hmn))
    refine ⟨L, fun m => ?_⟩
    have h := hL (e + m + 1)
    rw [SModEq.sub_mem, hmem] at h
    have h2 := Ideal.add_mem _ (hd d m (e + m + 1) (by omega)) h
    simpa using h2
  choose L hL using hlim
  have hfin : {d : σ →₀ ℕ | d.degree = t}.Finite :=
    (Finsupp.finite_of_degree_le t).subset fun d hd => le_of_eq hd
  let F₁ : MvPolynomial σ R := ∑ d ∈ hfin.toFinset, monomial d (L d)
  have hF₁ : F₁.IsHomogeneous t :=
    IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial _ (by simpa using hd)
  have hc : ∀ m d, coeff d ((s m).1 - F₁) ∈ I ^ (e + m + 1) := by
    intro m d
    by_cases hdt : d.degree = t
    · have : coeff d F₁ = L d := by
        simp only [F₁, coeff_sum, coeff_monomial]
        rw [Finset.sum_ite_eq']
        simp [hdt]
      rw [coeff_sub, this]
      exact hL d m
    · rw [((s m).2.1.sub hF₁).coeff_eq_zero hdt]
      exact Ideal.zero_mem _
  refine ⟨F₁, hF₁, fun m => hdesc _ hF₁ m e ?_, hc 0⟩
  rw [add_comm m e]
  have h := Ideal.sub_mem _ (s m).2.2 (hcoef _ _ (hc m))
  simpa using h
end GlobalTheory.Degen
