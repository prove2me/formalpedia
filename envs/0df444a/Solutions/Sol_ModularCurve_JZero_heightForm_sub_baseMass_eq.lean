-- Prove2me | solution 1 for ModularCurve.JZero.heightForm_sub_baseMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3d5e232b-f168-5de7-8e1f-af51857df951

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_heightForm_sub_baseMass_eq

set_option autoImplicit false

open AlgebraicCurve ModularCurve Finset

noncomputable section

namespace P2MQalg

variable {α : Type*}

open Classical in

noncomputable def QA (S : Finset α) (x t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) : ℝ :=
  (γ + (∑ v ∈ S, x v) - 1) * (∑ v ∈ S, x v * t v)
    - (∑ p ∈ S.offDiag, (x p.1 * x p.2) * bb p) / 2
    - (2 - 2 * γ) * (∑ v ∈ S, (x v * (x v - 1) / 2) * t v)

open Classical in

noncomputable def NF (S : Finset α) (x t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) : ℝ :=
  2 * γ * (∑ v ∈ S, x v ^ 2 * t v) + ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2 - bb p)

open Classical in
theorem sum_offDiag_eq_sub (S : Finset α) (G : α × α → ℝ) :
    ∑ p ∈ S.offDiag, G p = ∑ p ∈ S ×ˢ S, G p - ∑ p ∈ S.diag, G p := by
  rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag S)]; ring

open Classical in
theorem sum_offDiag_mul_mul_add (S : Finset α) (x t : α → ℝ) :
    ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2)
      = 2 * ((∑ v ∈ S, x v) * (∑ v ∈ S, x v * t v) - ∑ v ∈ S, x v ^ 2 * t v) := by
  rw [sum_offDiag_eq_sub, Finset.sum_product, Finset.sum_diag]
  have e1 : ∑ v ∈ S, ∑ w ∈ S, x v * x w * (t v + t w)
      = (∑ v ∈ S, x v * t v) * (∑ w ∈ S, x w) + (∑ v ∈ S, x v) * (∑ w ∈ S, x w * t w) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have e2 : ∑ v ∈ S, x v * x v * (t v + t v) = 2 * ∑ v ∈ S, x v ^ 2 * t v := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  rw [e1, e2]; ring

open Classical in
theorem two_mul_QA (S : Finset α) (x t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) :
    2 * QA S x t bb γ = NF S x t bb γ := by
  unfold QA NF
  have h3 : ∑ v ∈ S, (x v * (x v - 1) / 2) * t v
      = (∑ v ∈ S, x v ^ 2 * t v - ∑ v ∈ S, x v * t v) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h4 : ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2 - bb p)
      = ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2) - ∑ p ∈ S.offDiag, (x p.1 * x p.2) * bb p := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
  rw [h3, h4, sum_offDiag_mul_mul_add]
  ring

open Classical in
theorem NF_smul (S : Finset α) (x t : α → ℝ) (bb : α × α → ℝ) (γ c : ℝ) :
    NF S (fun v => c * x v) t bb γ = c ^ 2 * NF S x t bb γ := by
  unfold NF
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun v _ => by ring
  · exact Finset.sum_congr rfl fun p _ => by ring

open Classical in
theorem NF_parallelogram (S : Finset α) (x y t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) :
    NF S (fun v => x v + y v) t bb γ + NF S (fun v => x v - y v) t bb γ
      = 2 * NF S x t bb γ + 2 * NF S y t bb γ := by
  unfold NF
  have a1 : ∑ v ∈ S, (x v + y v) ^ 2 * t v + ∑ v ∈ S, (x v - y v) ^ 2 * t v
      = 2 * ∑ v ∈ S, x v ^ 2 * t v + 2 * ∑ v ∈ S, y v ^ 2 * t v := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have a2 : ∑ p ∈ S.offDiag, (x p.1 + y p.1) * (x p.2 + y p.2) * (t p.1 + t p.2 - bb p)
      + ∑ p ∈ S.offDiag, (x p.1 - y p.1) * (x p.2 - y p.2) * (t p.1 + t p.2 - bb p)
      = 2 * ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2 - bb p)
        + 2 * ∑ p ∈ S.offDiag, y p.1 * y p.2 * (t p.1 + t p.2 - bb p) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  linear_combination (2 * γ) * a1 + a2

open Classical in
theorem NF_singleton (v : α) (x t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) :
    NF {v} x t bb γ = 2 * γ * (x v ^ 2 * t v) := by
  unfold NF
  simp [Finset.offDiag_singleton]

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

open Classical in
theorem heightFormAux_eq_QA {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) (S : Finset (Place (AlgebraicClosure ℚ) F))
    (hS : D.support ⊆ S) :
    heightFormAux s γ b D = QA S (fun v => (D v : ℝ)) (baseHt s b) (fun p => pairHt s p.1 p.2) (γ : ℝ) := by
  unfold heightFormAux QA
  rw [Finsupp.sum_of_support_subset D hS (fun _ n => (n : ℝ)) (by intros; simp),
      Finsupp.sum_of_support_subset D hS (fun v n => (n : ℝ) * baseHt s b v) (by intros; simp),
      Finsupp.sum_of_support_subset D hS (fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * baseHt s b v)
        (by intros; simp)]
  rw [Finset.sum_subset (Finset.offDiag_mono hS)
        (f := fun p => ((D p.1 : ℝ) * (D p.2 : ℝ)) * pairHt s p.1 p.2) ?_]
  intro p hp hnp
  rw [Finset.mem_offDiag] at hp hnp
  have : D p.1 = 0 ∨ D p.2 = 0 := by
    by_contra h
    push Not at h
    exact hnp ⟨Finsupp.mem_support_iff.mpr h.1, Finsupp.mem_support_iff.mpr h.2, hp.2.2⟩
  rcases this with h | h <;> simp [h]

open Classical in

theorem two_mul_heightForm_eq_NF {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) (S : Finset (Place (AlgebraicClosure ℚ) F))
    (hS : (D.erase b).support ⊆ S) :
    2 * heightForm s γ b D
      = NF S (fun v => ((D.erase b) v : ℝ)) (baseHt s b) (fun p => pairHt s p.1 p.2) (γ : ℝ) := by
  unfold heightForm
  rw [heightFormAux_eq_QA s γ b _ S hS, two_mul_QA]

theorem erase_zsmul (b : Place (AlgebraicClosure ℚ) F) (m : ℤ) (D : Divisor (AlgebraicClosure ℚ) F) :
    (m • D).erase b = m • D.erase b := by
  ext v
  by_cases hv : v = b
  · subst hv; simp
  · simp [Finsupp.erase_ne hv]

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem heightForm_zsmul {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (m : ℤ) (D : Divisor (AlgebraicClosure ℚ) F) :
    heightForm s γ b (m • D) = (m : ℝ) ^ 2 * heightForm s γ b D := by
  classical
  have hS : ((m • D).erase b).support ⊆ (D.erase b).support := by
    rw [P2MQalg.erase_zsmul]; exact Finsupp.support_smul
  have h1 := P2MQalg.two_mul_heightForm_eq_NF s γ b (m • D) _ hS
  have h2 := P2MQalg.two_mul_heightForm_eq_NF s γ b D _ subset_rfl
  have hfun : (fun v => (((m • D).erase b) v : ℝ)) = fun v => (m : ℝ) * ((D.erase b) v : ℝ) := by
    funext v; rw [P2MQalg.erase_zsmul]; simp
  rw [hfun, P2MQalg.NF_smul, ← h2] at h1
  linarith

theorem heightForm_add_add_heightForm_sub {r : ℕ} (s : Fin r → F) (γ : ℤ)
    (b : Place (AlgebraicClosure ℚ) F) (D E : Divisor (AlgebraicClosure ℚ) F) :
    heightForm s γ b (D + E) + heightForm s γ b (D - E)
      = 2 * heightForm s γ b D + 2 * heightForm s γ b E := by
  classical
  set S := (D.erase b).support ∪ (E.erase b).support with hSdef
  have hD : (D.erase b).support ⊆ S := Finset.subset_union_left
  have hE : (E.erase b).support ⊆ S := Finset.subset_union_right
  have hDE : ((D + E).erase b).support ⊆ S := by
    rw [Finsupp.erase_add]; exact Finsupp.support_add.trans (Finset.union_subset hD hE)
  have hDE' : ((D - E).erase b).support ⊆ S := by
    rw [Finsupp.erase_sub]; exact Finsupp.support_sub.trans (Finset.union_subset hD hE)
  have h1 := P2MQalg.two_mul_heightForm_eq_NF s γ b (D + E) S hDE
  have h2 := P2MQalg.two_mul_heightForm_eq_NF s γ b (D - E) S hDE'
  have h3 := P2MQalg.two_mul_heightForm_eq_NF s γ b D S hD
  have h4 := P2MQalg.two_mul_heightForm_eq_NF s γ b E S hE
  have f1 : (fun v => (((D + E).erase b) v : ℝ)) = fun v => ((D.erase b) v : ℝ) + ((E.erase b) v : ℝ) := by
    funext v; rw [Finsupp.erase_add]; simp
  have f2 : (fun v => (((D - E).erase b) v : ℝ)) = fun v => ((D.erase b) v : ℝ) - ((E.erase b) v : ℝ) := by
    funext v; rw [Finsupp.erase_sub]; simp
  rw [f1] at h1; rw [f2] at h2
  have key := P2MQalg.NF_parallelogram S (fun v => ((D.erase b) v : ℝ)) (fun v => ((E.erase b) v : ℝ))
    (baseHt s b) (fun p => pairHt s p.1 p.2) (γ : ℝ)
  linarith

theorem heightForm_single {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    {v : Place (AlgebraicClosure ℚ) F} (hv : v ≠ b) (n : ℤ) :
    heightForm s γ b (Finsupp.single v n) = (γ : ℝ) * (n : ℝ) ^ 2 * baseHt s b v := by
  classical
  have he : (Finsupp.single v n).erase b = Finsupp.single v n := Finsupp.erase_single_ne (Ne.symm hv)
  have hS : ((Finsupp.single v n).erase b).support ⊆ {v} := by
    rw [he]; exact Finsupp.support_single_subset
  have h1 := P2MQalg.two_mul_heightForm_eq_NF s γ b (Finsupp.single v n) {v} hS
  rw [P2MQalg.NF_singleton, he, Finsupp.single_eq_same] at h1
  linarith

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem absLogHeight_nonneg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) :
    0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

theorem pointHt_nonneg {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    0 ≤ pointHt s v :=
  absLogHeight_nonneg _

theorem baseHt_le_pointHt_add_pointHt {r : ℕ} (s : Fin r → F) (b v : Place (AlgebraicClosure ℚ) F) :
    baseHt s b v ≤ pointHt s v + pointHt s b := by
  unfold baseHt
  split_ifs with h
  · exact add_nonneg (pointHt_nonneg s v) (pointHt_nonneg s b)
  · unfold pairHt
    linarith [absLogHeight_nonneg (chordVec s v b)]

end P2MQalg

namespace P2MQalg

variable {α : Type*}

open Classical in
theorem sum_offDiag_eq_sum_erase' (S : Finset α) (G : α × α → ℝ) :
    ∑ p ∈ S.offDiag, G p = ∑ v ∈ S, ∑ w ∈ S.erase v, G (v, w) := by
  rw [sum_offDiag_eq_sub, Finset.sum_product, Finset.sum_diag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.sum_erase_eq_sub hv]

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem offDiag_pairHt_eq_sum_sum {r : ℕ} (s : Fin r → F) (D : Divisor (AlgebraicClosure ℚ) F) :
    (∑ p ∈ D.support.offDiag, ((D p.1 : ℝ) * (D p.2 : ℝ)) * pairHt s p.1 p.2)
      = D.sum fun v n => (D.erase v).sum fun w k => (n : ℝ) * (k : ℝ) * pairHt s v w := by
  classical
  rw [sum_offDiag_eq_sum_erase']
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.support_erase]
  exact Finset.sum_congr rfl fun w hw => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hw)]

theorem heightForm_eq_sum_weight_mul_baseHt_sub {r : ℕ} (s : Fin r → F) (γ : ℤ)
    (b : Place (AlgebraicClosure ℚ) F) (D : Divisor (AlgebraicClosure ℚ) F) :
    heightForm s γ b D
      = ((D.erase b).sum fun v n =>
          (((γ : ℝ) + ((D.erase b).sum fun _ k => (k : ℝ)) - 1) * (n : ℝ)
            + (2 * (γ : ℝ) - 2) * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s b v)
        - ((D.erase b).sum fun v n => ((D.erase b).erase v).sum fun w k =>
            (n : ℝ) * (k : ℝ) * pairHt s v w) / 2 := by
  classical
  unfold heightForm heightFormAux
  rw [offDiag_pairHt_eq_sum_sum]
  have hW : ((D.erase b).sum fun v n =>
          (((γ : ℝ) + ((D.erase b).sum fun _ k => (k : ℝ)) - 1) * (n : ℝ)
            + (2 * (γ : ℝ) - 2) * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s b v)
      = ((γ : ℝ) + ((D.erase b).sum fun _ k => (k : ℝ)) - 1)
          * ((D.erase b).sum fun v n => (n : ℝ) * baseHt s b v)
        + (2 * (γ : ℝ) - 2) * ((D.erase b).sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * baseHt s b v) := by
    simp only [Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hW]; ring

theorem heightForm_sub_sum_mul_baseHt_eq {r : ℕ} (s : Fin r → F) (γ : ℤ)
    (b : Place (AlgebraicClosure ℚ) F) (D : Divisor (AlgebraicClosure ℚ) F) :
    heightForm s γ b D - ((D.erase b).sum fun v n => (n : ℝ) * baseHt s b v)
      = ((D.erase b).sum fun v n =>
          (((γ : ℝ) + ((D.erase b).sum fun _ k => (k : ℝ)) - 2) * (n : ℝ)
            + (2 * (γ : ℝ) - 2) * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s b v)
        - ((D.erase b).sum fun v n => ((D.erase b).erase v).sum fun w k =>
            (n : ℝ) * (k : ℝ) * pairHt s v w) / 2 := by
  classical
  rw [heightForm_eq_sum_weight_mul_baseHt_sub]
  have : ((D.erase b).sum fun v n =>
          (((γ : ℝ) + ((D.erase b).sum fun _ k => (k : ℝ)) - 2) * (n : ℝ)
            + (2 * (γ : ℝ) - 2) * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s b v)
      = ((D.erase b).sum fun v n =>
          (((γ : ℝ) + ((D.erase b).sum fun _ k => (k : ℝ)) - 1) * (n : ℝ)
            + (2 * (γ : ℝ) - 2) * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s b v)
        - ((D.erase b).sum fun v n => (n : ℝ) * baseHt s b v) := by
    simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [this]; ring

section LevelN3
variable (N : ℕ) [NeZero N]

theorem JZero_offBaseMass_cast (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (JZero.offBaseMass N D : ℝ) = (D.erase (cuspInftyBar N)).sum fun _ k => (k : ℝ) := by
  simp only [JZero.offBaseMass, Finsupp.sum, Int.cast_sum]

theorem JZero_heightForm_eq_sum_weight_mul_baseHt_sub {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    JZero.heightForm N s D
      = ((D.erase (cuspInftyBar N)).sum fun v n =>
          (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
              + (JZero.offBaseMass N D : ℝ) - 1) * (n : ℝ)
            + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
              * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
        - ((D.erase (cuspInftyBar N)).sum fun v n => ((D.erase (cuspInftyBar N)).erase v).sum fun w k =>
            (n : ℝ) * (k : ℝ) * pairHt s v w) / 2 := by
  rw [JZero_offBaseMass_cast]
  exact heightForm_eq_sum_weight_mul_baseHt_sub s _ _ D

theorem JZero_heightForm_sub_baseMass_eq {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    JZero.heightForm N s D - JZero.baseMass N s D
      = ((D.erase (cuspInftyBar N)).sum fun v n =>
          (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
              + (JZero.offBaseMass N D : ℝ) - 2) * (n : ℝ)
            + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
              * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
        - ((D.erase (cuspInftyBar N)).sum fun v n => ((D.erase (cuspInftyBar N)).erase v).sum fun w k =>
            (n : ℝ) * (k : ℝ) * pairHt s v w) / 2 := by
  rw [JZero_offBaseMass_cast]
  exact heightForm_sub_sum_mul_baseHt_eq s _ _ D

end LevelN3
end P2MQalg

end

theorem solution (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    JZero.heightForm N s D - JZero.baseMass N s D
      = ((D.erase (cuspInftyBar N)).sum fun v n =>
          (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
              + (JZero.offBaseMass N D : ℝ) - 2) * (n : ℝ)
            + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
              * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
        - ((D.erase (cuspInftyBar N)).sum fun v n => ((D.erase (cuspInftyBar N)).erase v).sum fun w k =>
            (n : ℝ) * (k : ℝ) * pairHt s v w) / 2 :=
  P2MQalg.JZero_heightForm_sub_baseMass_eq N s D

end S_ModularCurve_JZero_heightForm_sub_baseMass_eq
end P2MW
export P2MW.S_ModularCurve_JZero_heightForm_sub_baseMass_eq (solution)
