-- Prove2me | solution 1 for HardyFLocal.product_lattice_trace
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:52:46.733046+00:00
-- url     : https://prove2.me/submissions/8504c20d-b9ad-4bf7-ae18-ea6f2220ce0b

import Mathlib
import Definitions.Def_HardyFLocal_Lattice
import Theorems.Thm_HardyFLocal_prodOp_apply_kron
open HardyCausaloid
namespace HardyFLocal
open scoped Kronecker Matrix
variable {m n : ℕ}

private def wireTensor (A : Q m n → Matrix (Fin 2) (Fin 2) ℂ) : GlobalMat m n :=
  Matrix.of fun c d => ∏ q, A q (c q) (d q)

private theorem wireTensor_entries (x : X m n) (A : Q m n → Matrix (Fin 2) (Fin 2) ℂ)
    (c d : Q m n → Fin 2) :
    wireTensor A c d = (∏ u ∈ Finset.univ.erase x.1, A (.inl u) (c (.inl u)) (d (.inl u))) *
      (∏ v ∈ Finset.univ.erase x.2, A (.inr v) (c (.inr v)) (d (.inr v))) *
      (A (.inl x.1) (c (.inl x.1)) (d (.inl x.1)) * A (.inr x.2) (c (.inr x.2)) (d (.inr x.2))) := by
  classical
  unfold wireTensor
  simp only [Matrix.of_apply, Fintype.prod_sum_type]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x.1),
    ← Finset.mul_prod_erase _ (fun v => A (.inr v) (c (.inr v)) (d (.inr v))) (Finset.mem_univ x.2)]
  ring

private theorem embed_product_on_wires (x : X m n) (F G : Op (Fin 2))
    (A : Q m n → Matrix (Fin 2) (Fin 2) ℂ) :
    embed x (prodOp F G) (wireTensor A) = wireTensor
      (Function.update (Function.update A (.inl x.1) (F (A (.inl x.1)))) (.inr x.2) (G (A (.inr x.2)))) := by
  classical
  apply Matrix.ext
  intro c d
  let rest := (∏ u ∈ Finset.univ.erase x.1, A (.inl u) (c (.inl u)) (d (.inl u))) *
      (∏ v ∈ Finset.univ.erase x.2, A (.inr v) (c (.inr v)) (d (.inr v)))
  have hslice : slice x c d (wireTensor A) = rest • (A (.inl x.1) ⊗ₖ A (.inr x.2)) := by
    apply Matrix.ext
    rintro ⟨i,j⟩ ⟨k,l⟩
    change wireTensor A (setPair x c (i,j)) (setPair x d (k,l)) = rest * (A (.inl x.1) i k * A (.inr x.2) j l)
    rw [wireTensor_entries x]
    simp [setPair, Function.update_apply, rest]
    left
    congr 1 <;> apply Finset.prod_congr rfl <;> intro z hz <;> simp [(Finset.mem_erase.mp hz).1]
  change (prodOp F G (slice x c d (wireTensor A))) _ _ = _
  rw [hslice, map_smul, prodOp_apply_kron, wireTensor_entries x]
  simp [Function.update_apply, rest]
  left
  congr 1 <;> apply Finset.prod_congr rfl <;> intro z hz <;> simp [(Finset.mem_erase.mp hz).1]


private theorem wireTensor_trace (A : Q m n → Matrix (Fin 2) (Fin 2) ℂ) :
    (wireTensor A).trace = ∏ q, (A q).trace := by
  classical
  change (∑ c : Q m n → Fin 2, ∏ q, A q (c q) (c q)) = ∏ q, ∑ i, A q i i
  exact (Fintype.prod_sum fun q i => A q i i).symm

private theorem wireTensor_unit (c d : Q m n → Fin 2) :
    wireTensor (fun q => Matrix.single (c q) (d q) (1 : ℂ)) = Matrix.single c d 1 := by
  classical
  apply Matrix.ext
  intro u v
  change (∏ q, Matrix.single (c q) (d q) (1 : ℂ) (u q) (v q)) = _
  by_cases hu : c = u
  · subst u
    by_cases hv : d = v
    · subst v; simp
    · obtain ⟨q,hq⟩ := Function.ne_iff.mp hv
      rw [Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])]
      simp [hv]
  · obtain ⟨q,hq⟩ := Function.ne_iff.mp hu
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])]
    simp [hu]

private noncomputable def wireStep (x : X m n) (F G : Op (Fin 2))
    (q : Q m n) : Op (Fin 2) :=
  if q = .inl x.1 then F else if q = .inr x.2 then G else LinearMap.id

private theorem fold_wires (V : List (X m n)) (F G : X m n → Op (Fin 2))
    (A : Q m n → Matrix (Fin 2) (Fin 2) ℂ) :
    V.foldl (fun B x => embed x (prodOp (F x) (G x)) B) (wireTensor A) =
      wireTensor (fun q => V.foldl (fun B x => wireStep x (F x) (G x) q B) (A q)) := by
  classical
  induction V generalizing A with
  | nil => rfl
  | cons x V ih =>
    simp only [List.foldl_cons, embed_product_on_wires, ih]
    congr 1
    funext q
    congr 1
    by_cases h : q = .inl x.1
    · subst q; simp [wireStep]
    · by_cases h' : q = .inr x.2
      · subst q; simp [wireStep]
      · simp [wireStep,h,h']

private noncomputable def evolutionMap (V : List (X m n))
    (T : X m n → Op (Fin 2 × Fin 2)) : Op (Q m n → Fin 2) :=
  match V with
  | [] => LinearMap.id
  | x :: vs => evolutionMap vs T ∘ₗ embed x (T x)

private theorem evolutionMap_apply (V : List (X m n)) (T : X m n → Op (Fin 2 × Fin 2))
    (A : GlobalMat m n) :
    evolutionMap V T A = V.foldl (fun B x => embed x (T x) B) A := by
  induction V generalizing A with
  | nil => rfl
  | cons x V ih => exact ih _

open HardyCausaloid
end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {m n : ℕ} (ρ : GlobalMat m n)
    (t : ∀ x, Label (Setting m n) (Outcome m n) x) (F G : X m n → Op (Fin 2))
    (h : ∀ x, labelOp (t x) = prodOp (F x) (G x)) :
    latticeProb ρ t = (∑ c, ∑ d, ρ c d * ∏ q : Q m n,
      ((vertexList m n).foldl (fun B x =>
        (if q = .inl x.1 then F x else if q = .inr x.2 then G x else LinearMap.id) B)
        (Matrix.single (c q) (d q) (1 : ℂ))).trace).re := by
  classical
  let V := vertexList m n
  let T x := prodOp (F x) (G x)
  have htotal : evolve ρ t = evolutionMap V T ρ := by
    simp only [evolve, h, evolutionMap_apply, T, V]
  unfold latticeProb
  rw [htotal]
  conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
  simp only [map_sum, Matrix.trace_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [show Matrix.single c d (ρ c d) = ρ c d • Matrix.single c d (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul,mul_one], map_smul, Matrix.trace_smul, smul_eq_mul,
    ← wireTensor_unit, evolutionMap_apply, fold_wires, wireTensor_trace]
  rfl

