-- Prove2me | solution 1 for GlobalTheory.UnipotentDecomposition.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:17.225682+00:00
-- url     : https://prove2.me/submissions/ae171da5-b749-4f67-9081-fce9b2fc8ec2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Theorems.Thm_GlobalTheory_UnipotentDecomposition_udl_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentDecomposition
open Matrix
namespace GlobalTheory.UnipotentDecomposition
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] {α β : O} (hab : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
      (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        (∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)) ∧
        (∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)) ∧
        g = (u * Matrix.diagonal fun i => (d i : O)) * l ∧ ∀ i, α * β ∣ (d i : O) - g i i := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    refine ⟨1, fun i => i.elim0, 1, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    ext i; exact i.elim0
  | succ n ih =>
    intro g hg hu
    set a : Oˣ := (hu (Fin.last n)).unit with ha
    have haa : (a : O) = g (Fin.last n) (Fin.last n) := IsUnit.unit_spec _
    have hinv : (↑a⁻¹ : O) * ↑a = 1 := Units.inv_mul a
    set r : Fin n → O := fun i => g i.castSucc (Fin.last n) with hr_def
    set c : Fin n → O := fun j => g (Fin.last n) j.castSucc with hc_def
    set G : Matrix (Fin n) (Fin n) O := fun i j => g i.castSucc j.castSucc - r i * ↑a⁻¹ * c j with hG_def
    have hr : ∀ i, α ∣ r i := fun i => (hg i.castSucc (Fin.last n)).1 (Fin.castSucc_lt_last i)
    have hc : ∀ j, β ∣ c j := fun j => (hg (Fin.last n) j.castSucc).2 (Fin.castSucc_lt_last j)
    have hG : ∀ i j, (i < j → α ∣ G i j) ∧ (j < i → β ∣ G i j) := by
      intro i j
      constructor
      · intro h
        exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right (hr i) _) _)
      · intro h
        exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_left (hc j) _)
    have hrc : ∀ i, α * β ∣ r i * ↑a⁻¹ * c i := by
      intro i
      rw [show r i * ↑a⁻¹ * c i = r i * c i * ↑a⁻¹ by ring]
      exact Dvd.dvd.mul_right (mul_dvd_mul (hr i) (hc i)) _
    have hGu : ∀ i, IsUnit (G i i) := by
      intro i
      by_contra h
      have h1 : r i * ↑a⁻¹ * c i ∈ nonunits O := fun hu' => hab (isUnit_of_dvd_unit (hrc i) hu')
      have h2 := IsLocalRing.nonunits_add (show G i i ∈ nonunits O from h) h1
      have h3 : G i i + r i * ↑a⁻¹ * c i = g i.castSucc i.castSucc := sub_add_cancel _ _
      rw [h3] at h2
      exact h2 (hu _)
    obtain ⟨U, D, L, hU, hL, hUDL, hD⟩ := ih G hG hGu
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j)
              (fun i' => Fin.lastCases (motive := fun _ => O) (r i' * ↑a⁻¹) (fun j' => U i' j') j) i,
            fun i => Fin.lastCases (motive := fun _ => Oˣ) a D i,
            Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun j' => ↑a⁻¹ * c j') j)
              (fun i' => Fin.lastCases (motive := fun _ => O) 0 (fun j' => L i' j') j) i,
            ?_, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
        first | exact hr i | exact (hr i).mul_right _
      · simpa using hU i j
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
        first | exact hc j | exact (hc j).mul_left _
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
      · simpa using hL i j
    · ext i j
      rw [udl_apply, Fin.sum_univ_castSucc]
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [haa]
      · simp [c]
        done
      · simp [r]
        done
      · have e := congrFun (congrFun hUDL i) j
        rw [udl_apply] at e
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero, mul_one]
        rw [← e]
        simp only [G]
        linear_combination (-(r i * ↑a⁻¹ * c j)) * hinv
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [haa]
      · have e : ((D i : O)) - g i.castSucc i.castSucc = ((D i : O) - G i i) - r i * ↑a⁻¹ * c i := by
          simp [G]; ring
        simpa [e] using dvd_sub (hD i) (hrc i)
end GlobalTheory.UnipotentDecomposition
