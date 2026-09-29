-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_archDeriv_and_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d26dfaa0-82b5-535c-94ce-f63f22d0d6b4

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_LanglandsTunnell_CubicInduction_EnvelopingAction3
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

section Centrality

open LanglandsTunnell.CubicInduction.WhittakerBlock (archDerivₗ)

private theorem archDerivₗ_mul_sub (a b c d : Fin 3) :
    archDerivₗ a b * archDerivₗ c d -
        archDerivₗ c d * archDerivₗ a b =
      (if b = c then archDerivₗ a d else 0) -
        (if d = a then archDerivₗ c b else 0) := by
  have h : WhittakerBlock.derivAction3
        (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ) -
          Matrix.single c d (1 : ℂ) * Matrix.single a b (1 : ℂ)) =
      WhittakerBlock.derivAction3 (Matrix.single a b (1 : ℂ)) *
          WhittakerBlock.derivAction3 (Matrix.single c d (1 : ℂ)) -
        WhittakerBlock.derivAction3 (Matrix.single c d (1 : ℂ)) *
          WhittakerBlock.derivAction3 (Matrix.single a b (1 : ℂ)) :=
    WhittakerBlock.derivAction3_lie (Matrix.single a b (1 : ℂ)) (Matrix.single c d (1 : ℂ))
  rw [map_sub, WhittakerBlock.derivAction3_single, WhittakerBlock.derivAction3_single] at h
  rw [← h]
  congr 1
  · by_cases hbc : b = c
    · subst hbc
      rw [Matrix.single_mul_single_same, one_mul, if_pos rfl, WhittakerBlock.derivAction3_single]
    · rw [Matrix.single_mul_single_of_ne (1 : ℂ) a b c hbc (1 : ℂ), map_zero, if_neg hbc]
  · by_cases hda : d = a
    · subst hda
      rw [Matrix.single_mul_single_same, one_mul, if_pos rfl, WhittakerBlock.derivAction3_single]
    · rw [Matrix.single_mul_single_of_ne (1 : ℂ) c d a hda (1 : ℂ), map_zero, if_neg hda]

private theorem archDerivₗ_swap (a b c d : Fin 3) :
    archDerivₗ a b * archDerivₗ c d =
      archDerivₗ c d * archDerivₗ a b +
        ((if b = c then archDerivₗ a d else 0) -
          (if d = a then archDerivₗ c b else 0)) := by
  rw [← archDerivₗ_mul_sub a b c d]
  abel

private theorem archDerivₗ_swap_mul (a b c d : Fin 3) (w : Module.End ℂ WhittakerBlock.smoothFunctions3) :
    archDerivₗ a b * (archDerivₗ c d * w) =
      archDerivₗ c d * (archDerivₗ a b * w) +
        ((if b = c then archDerivₗ a d else 0) -
          (if d = a then archDerivₗ c b else 0)) * w := by
  rw [← mul_assoc, archDerivₗ_swap a b c d, add_mul, mul_assoc]

private noncomputable def cas2ₗ : Module.End ℂ WhittakerBlock.smoothFunctions3 :=
  ∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * archDerivₗ j i

private theorem end_mul_add (w x y : Module.End ℂ WhittakerBlock.smoothFunctions3) : w * (x + y) = w * x + w * y :=
  mul_add w x y

private theorem end_mul_sub (w x y : Module.End ℂ WhittakerBlock.smoothFunctions3) : w * (x - y) = w * x - w * y :=
  mul_sub w x y

private theorem end_sub_mul (x y w : Module.End ℂ WhittakerBlock.smoothFunctions3) : (x - y) * w = x * w - y * w :=
  sub_mul x y w

private theorem end_mul_ite (P : Prop) [Decidable P] (w x : Module.End ℂ WhittakerBlock.smoothFunctions3) :
    (w * if P then x else 0) = if P then w * x else 0 := by
  split_ifs
  · rfl
  · exact mul_zero w

private theorem end_ite_mul (P : Prop) [Decidable P] (x w : Module.End ℂ WhittakerBlock.smoothFunctions3) :
    ((if P then x else 0) * w) = if P then x * w else 0 := by
  split_ifs
  · rfl
  · exact zero_mul w

private theorem cas2_summand (a b i j : Fin 3) :
    archDerivₗ a b * (archDerivₗ i j * archDerivₗ j i) +
          (if j = a then archDerivₗ i b * archDerivₗ j i else 0) +
        (if i = a then archDerivₗ i j * archDerivₗ j b else 0) =
      archDerivₗ i j * (archDerivₗ j i * archDerivₗ a b) +
          (if b = i then archDerivₗ a j * archDerivₗ j i else 0) +
        (if b = j then archDerivₗ i j * archDerivₗ a i else 0) := by
  rw [archDerivₗ_swap_mul a b i j, archDerivₗ_swap a b j i]
  simp only [end_mul_add, end_mul_sub, end_sub_mul, end_mul_ite, end_ite_mul]
  abel

private theorem cas2_piece₁ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        if b = i then archDerivₗ a j * archDerivₗ j i else 0) =
      ∑ j : Fin 3, archDerivₗ a j * archDerivₗ j b := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem cas2_piece₂ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        if j = a then archDerivₗ i b * archDerivₗ j i else 0) =
      ∑ i : Fin 3, archDerivₗ i b * archDerivₗ a i := by
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem cas2_piece₃ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        if b = j then archDerivₗ i j * archDerivₗ a i else 0) =
      ∑ i : Fin 3, archDerivₗ i b * archDerivₗ a i := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem cas2_piece₄ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        if i = a then archDerivₗ i j * archDerivₗ j b else 0) =
      ∑ j : Fin 3, archDerivₗ a j * archDerivₗ j b := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem end_add_right_cancel {x y z : Module.End ℂ WhittakerBlock.smoothFunctions3} (h : x + z = y + z) :
    x = y := by
  refine LinearMap.ext fun v => ?_
  have hv := LinearMap.congr_fun h v
  simp only [LinearMap.add_apply] at hv
  exact add_right_cancel hv

private theorem archDerivₗ_mul_cas2ₗ (a b : Fin 3) :
    archDerivₗ a b * cas2ₗ = cas2ₗ * archDerivₗ a b := by
  have hA : archDerivₗ a b * cas2ₗ = ∑ i : Fin 3, ∑ j : Fin 3,
      archDerivₗ a b * (archDerivₗ i j * archDerivₗ j i) := by
    simp only [cas2ₗ, Finset.mul_sum]
  have hB : cas2ₗ * archDerivₗ a b = ∑ i : Fin 3, ∑ j : Fin 3,
      archDerivₗ i j * (archDerivₗ j i * archDerivₗ a b) := by
    simp only [cas2ₗ, Finset.sum_mul, mul_assoc]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun i _ =>
    Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun j _ => cas2_summand a b i j
  simp only [Finset.sum_add_distrib] at hsum
  rw [cas2_piece₂, cas2_piece₄, cas2_piece₁, cas2_piece₃] at hsum
  rw [hA, hB]
  refine end_add_right_cancel (z := (∑ i : Fin 3, archDerivₗ i b * archDerivₗ a i) +
    ∑ j : Fin 3, archDerivₗ a j * archDerivₗ j b) ?_
  rw [← add_assoc, hsum]
  abel

private theorem casimir2_eq_cas2ₗ (φ : WhittakerBlock.smoothFunctions3) :
    WhittakerBlock.casimir2 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = ((cas2ₗ φ : WhittakerBlock.smoothFunctions3) :
      AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  funext g
  simp only [WhittakerBlock.casimir2, cas2ₗ, LinearMap.sum_apply, Submodule.coe_sum, Module.End.mul_apply,
    WhittakerBlock.coe_archDerivₗ_apply, Finset.sum_apply]

private theorem casimir2_archDeriv (a b : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : WhittakerBlock.IsArchSmooth3 φ) :
    WhittakerBlock.casimir2 (WhittakerBlock.archDeriv a b φ) =
      WhittakerBlock.archDeriv a b (WhittakerBlock.casimir2 φ) := by
  have h₁ : WhittakerBlock.archDeriv a b φ =
      ((archDerivₗ a b ⟨φ, hφ⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := rfl
  have h₂ : WhittakerBlock.casimir2 φ =
      ((cas2ₗ ⟨φ, hφ⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    casimir2_eq_cas2ₗ ⟨φ, hφ⟩
  have hcomm := congrArg (fun T : Module.End ℂ WhittakerBlock.smoothFunctions3 => T ⟨φ, hφ⟩)
    (archDerivₗ_mul_cas2ₗ a b)
  simp only [Module.End.mul_apply] at hcomm
  rw [h₁, casimir2_eq_cas2ₗ, h₂, ← WhittakerBlock.coe_archDerivₗ_apply, hcomm]

private noncomputable def cas1ₗ : Module.End ℂ WhittakerBlock.smoothFunctions3 :=
  ∑ i : Fin 3, archDerivₗ i i

private theorem cas1_summand (a b i : Fin 3) :
    archDerivₗ a b * archDerivₗ i i + (if i = a then archDerivₗ i b else 0) =
      archDerivₗ i i * archDerivₗ a b + (if b = i then archDerivₗ a i else 0) := by
  rw [archDerivₗ_swap a b i i]
  abel

private theorem archDerivₗ_mul_cas1ₗ (a b : Fin 3) :
    archDerivₗ a b * cas1ₗ = cas1ₗ * archDerivₗ a b := by
  have hA : archDerivₗ a b * cas1ₗ = ∑ i : Fin 3, archDerivₗ a b * archDerivₗ i i := by
    simp only [cas1ₗ, Finset.mul_sum]
  have hB : cas1ₗ * archDerivₗ a b = ∑ i : Fin 3, archDerivₗ i i * archDerivₗ a b := by
    simp only [cas1ₗ, Finset.sum_mul]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun i _ => cas1_summand a b i
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  rw [hA, hB]
  exact end_add_right_cancel hsum

private theorem casimir1_eq_cas1ₗ (φ : WhittakerBlock.smoothFunctions3) :
    WhittakerBlock.casimir1 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = ((cas1ₗ φ : WhittakerBlock.smoothFunctions3) :
      AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  funext g
  simp only [WhittakerBlock.casimir1, cas1ₗ, LinearMap.sum_apply, Submodule.coe_sum,
    WhittakerBlock.coe_archDerivₗ_apply, Finset.sum_apply]

private theorem casimir1_archDeriv (a b : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : WhittakerBlock.IsArchSmooth3 φ) :
    WhittakerBlock.casimir1 (WhittakerBlock.archDeriv a b φ) =
      WhittakerBlock.archDeriv a b (WhittakerBlock.casimir1 φ) := by
  have h₁ : WhittakerBlock.archDeriv a b φ =
      ((archDerivₗ a b ⟨φ, hφ⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := rfl
  have h₂ : WhittakerBlock.casimir1 φ =
      ((cas1ₗ ⟨φ, hφ⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    casimir1_eq_cas1ₗ ⟨φ, hφ⟩
  have hcomm := congrArg (fun T : Module.End ℂ WhittakerBlock.smoothFunctions3 => T ⟨φ, hφ⟩)
    (archDerivₗ_mul_cas1ₗ a b)
  simp only [Module.End.mul_apply] at hcomm
  rw [h₁, casimir1_eq_cas1ₗ, h₂, ← WhittakerBlock.coe_archDerivₗ_apply, hcomm]

private noncomputable def cas3ₗ : Module.End ℂ WhittakerBlock.smoothFunctions3 :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ i j * (archDerivₗ j k * archDerivₗ k i)

private theorem cas3_summand (a b i j k : Fin 3) :
    archDerivₗ a b * (archDerivₗ i j * (archDerivₗ j k * archDerivₗ k i)) +
          (if j = a then archDerivₗ i b * (archDerivₗ j k * archDerivₗ k i) else 0) +
        (if k = a then archDerivₗ i j * (archDerivₗ j b * archDerivₗ k i) else 0) +
      (if i = a then archDerivₗ i j * (archDerivₗ j k * archDerivₗ k b) else 0) =
      archDerivₗ i j * (archDerivₗ j k * (archDerivₗ k i * archDerivₗ a b)) +
          (if b = i then archDerivₗ a j * (archDerivₗ j k * archDerivₗ k i) else 0) +
        (if b = j then archDerivₗ i j * (archDerivₗ a k * archDerivₗ k i) else 0) +
      (if b = k then archDerivₗ i j * (archDerivₗ j k * archDerivₗ a i) else 0) := by
  rw [archDerivₗ_swap_mul a b i j, archDerivₗ_swap_mul a b j k, archDerivₗ_swap a b k i]
  simp only [end_mul_add, end_mul_sub, end_sub_mul, end_mul_ite, end_ite_mul]
  abel

private theorem cas3_piece₁ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if b = i then archDerivₗ a j * (archDerivₗ j k * archDerivₗ k i) else 0)) =
      ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ a j * (archDerivₗ j k * archDerivₗ k b) := by
  rw [Finset.sum_eq_single b]
  · simp only [if_true]
  · intro i _ hi
    simp only [hi.symm, if_false, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

private theorem cas3_piece₂ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if j = a then archDerivₗ i b * (archDerivₗ j k * archDerivₗ k i) else 0)) =
      ∑ i : Fin 3, ∑ k : Fin 3, archDerivₗ i b * (archDerivₗ a k * archDerivₗ k i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem cas3_piece₃ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if b = j then archDerivₗ i j * (archDerivₗ a k * archDerivₗ k i) else 0)) =
      ∑ i : Fin 3, ∑ k : Fin 3, archDerivₗ i b * (archDerivₗ a k * archDerivₗ k i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem cas3_piece₄ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if k = a then archDerivₗ i j * (archDerivₗ j b * archDerivₗ k i) else 0)) =
      ∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * (archDerivₗ j b * archDerivₗ a i) := by
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem cas3_piece₅ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if b = k then archDerivₗ i j * (archDerivₗ j k * archDerivₗ a i) else 0)) =
      ∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * (archDerivₗ j b * archDerivₗ a i) := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem cas3_piece₆ (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (if i = a then archDerivₗ i j * (archDerivₗ j k * archDerivₗ k b) else 0)) =
      ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ a j * (archDerivₗ j k * archDerivₗ k b) := by
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
  · intro i _ hi
    simp only [hi, if_false, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem archDerivₗ_mul_cas3ₗ (a b : Fin 3) :
    archDerivₗ a b * cas3ₗ = cas3ₗ * archDerivₗ a b := by
  have hA : archDerivₗ a b * cas3ₗ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      archDerivₗ a b * (archDerivₗ i j * (archDerivₗ j k * archDerivₗ k i)) := by
    simp only [cas3ₗ, Finset.mul_sum]
  have hB : cas3ₗ * archDerivₗ a b = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      archDerivₗ i j * (archDerivₗ j k * (archDerivₗ k i * archDerivₗ a b)) := by
    simp only [cas3ₗ, Finset.sum_mul, mul_assoc]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun i _ =>
    Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun j _ =>
      Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl fun k _ => cas3_summand a b i j k
  simp only [Finset.sum_add_distrib] at hsum
  rw [cas3_piece₂, cas3_piece₄, cas3_piece₆, cas3_piece₁, cas3_piece₃, cas3_piece₅] at hsum
  rw [hA, hB]
  refine end_add_right_cancel
    (z := (∑ i : Fin 3, ∑ k : Fin 3, archDerivₗ i b * (archDerivₗ a k * archDerivₗ k i)) +
      (∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * (archDerivₗ j b * archDerivₗ a i)) +
        ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ a j * (archDerivₗ j k * archDerivₗ k b)) ?_
  rw [← add_assoc, ← add_assoc, hsum]
  abel

private theorem casimir3_eq_cas3ₗ (φ : WhittakerBlock.smoothFunctions3) :
    WhittakerBlock.casimir3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = ((cas3ₗ φ : WhittakerBlock.smoothFunctions3) :
      AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  funext g
  simp only [WhittakerBlock.casimir3, cas3ₗ, LinearMap.sum_apply, Submodule.coe_sum, Module.End.mul_apply,
    WhittakerBlock.coe_archDerivₗ_apply, Finset.sum_apply]

private theorem casimir3_archDeriv (a b : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : WhittakerBlock.IsArchSmooth3 φ) :
    WhittakerBlock.casimir3 (WhittakerBlock.archDeriv a b φ) =
      WhittakerBlock.archDeriv a b (WhittakerBlock.casimir3 φ) := by
  have h₁ : WhittakerBlock.archDeriv a b φ =
      ((archDerivₗ a b ⟨φ, hφ⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := rfl
  have h₂ : WhittakerBlock.casimir3 φ =
      ((cas3ₗ ⟨φ, hφ⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    casimir3_eq_cas3ₗ ⟨φ, hφ⟩
  have hcomm := congrArg (fun T : Module.End ℂ WhittakerBlock.smoothFunctions3 => T ⟨φ, hφ⟩)
    (archDerivₗ_mul_cas3ₗ a b)
  simp only [Module.End.mul_apply] at hcomm
  rw [h₁, casimir3_eq_cas3ₗ, h₂, ← WhittakerBlock.coe_archDerivₗ_apply, hcomm]

private theorem cas1ₗ_comm_cas2ₗ : Commute cas1ₗ cas2ₗ := by
  unfold cas1ₗ
  exact Commute.sum_left _ _ _ fun a _ => archDerivₗ_mul_cas2ₗ a a

private theorem cas1ₗ_comm_cas3ₗ : Commute cas1ₗ cas3ₗ := by
  unfold cas1ₗ
  exact Commute.sum_left _ _ _ fun a _ => archDerivₗ_mul_cas3ₗ a a

private theorem cas2ₗ_comm_cas3ₗ : Commute cas2ₗ cas3ₗ := by
  unfold cas2ₗ
  exact Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ =>
    Commute.mul_left (archDerivₗ_mul_cas3ₗ a b) (archDerivₗ_mul_cas3ₗ b a)

private theorem casimir_comm (H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hH : WhittakerBlock.IsArchSmooth3 H) :
    WhittakerBlock.casimir1 (WhittakerBlock.casimir2 H) = WhittakerBlock.casimir2 (WhittakerBlock.casimir1 H) ∧
      WhittakerBlock.casimir1 (WhittakerBlock.casimir3 H) = WhittakerBlock.casimir3 (WhittakerBlock.casimir1 H) ∧
        WhittakerBlock.casimir2 (WhittakerBlock.casimir3 H) = WhittakerBlock.casimir3 (WhittakerBlock.casimir2 H) := by
  have h1 : WhittakerBlock.casimir1 H = ((cas1ₗ ⟨H, hH⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    casimir1_eq_cas1ₗ ⟨H, hH⟩
  have h2 : WhittakerBlock.casimir2 H = ((cas2ₗ ⟨H, hH⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    casimir2_eq_cas2ₗ ⟨H, hH⟩
  have h3 : WhittakerBlock.casimir3 H = ((cas3ₗ ⟨H, hH⟩ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    casimir3_eq_cas3ₗ ⟨H, hH⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, h1, casimir1_eq_cas1ₗ, casimir2_eq_cas2ₗ]
    exact congrArg _ (congrArg (fun T : Module.End ℂ WhittakerBlock.smoothFunctions3 => T ⟨H, hH⟩) cas1ₗ_comm_cas2ₗ.eq)
  · rw [h3, h1, casimir1_eq_cas1ₗ, casimir3_eq_cas3ₗ]
    exact congrArg _ (congrArg (fun T : Module.End ℂ WhittakerBlock.smoothFunctions3 => T ⟨H, hH⟩) cas1ₗ_comm_cas3ₗ.eq)
  · rw [h3, h2, casimir2_eq_cas2ₗ, casimir3_eq_cas3ₗ]
    exact congrArg _ (congrArg (fun T : Module.End ℂ WhittakerBlock.smoothFunctions3 => T ⟨H, hH⟩) cas2ₗ_comm_cas3ₗ.eq)

end Centrality

open LanglandsTunnell.CubicInduction.WhittakerBlock in

theorem solution
    (H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hH : WhittakerBlock.IsArchSmooth3 H) :
    (∀ i j : Fin 3,
      casimir1 (archDeriv i j H) = archDeriv i j (casimir1 H) ∧
        casimir2 (archDeriv i j H) = archDeriv i j (casimir2 H) ∧
          casimir3 (archDeriv i j H) = archDeriv i j (casimir3 H)) ∧
      casimir1 (casimir2 H) = casimir2 (casimir1 H) ∧
        casimir1 (casimir3 H) = casimir3 (casimir1 H) ∧
          casimir2 (casimir3 H) = casimir3 (casimir2 H) := by
  exact ⟨fun i j => ⟨casimir1_archDeriv i j H hH, casimir2_archDeriv i j H hH, casimir3_archDeriv i j H hH⟩,
    (casimir_comm H hH).1, (casimir_comm H hH).2.1, (casimir_comm H hH).2.2⟩

end S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm (solution)
