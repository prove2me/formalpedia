-- Prove2me | solution 1 for HardyFLocal.grid_region_expansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:57:46.166663+00:00
-- url     : https://prove2.me/submissions/66f66f71-e995-4c8e-ab64-7ff7f6cf5f70

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_eq20_two_qubit_expansion
import Theorems.Thm_HardyCausaloid_product_reconstruction
open HardyCausaloid
namespace HardyFLocal
open HardyCausaloid
variable {m n : ℕ}

private noncomputable def circuit (V : List (X m n)) (f : X m n → Op (Fin 2 × Fin 2)) :
    Op (Q m n → Fin 2) := match V with
  | [] => LinearMap.id
  | x :: xs => circuit xs f ∘ₗ embed x (f x)

private theorem circuit_fold (V : List (X m n)) (f : X m n → Op (Fin 2 × Fin 2)) (A : GlobalMat m n) :
    circuit V f A = V.foldl (fun B x => embed x (f x) B) A := by
  induction V generalizing A with
  | nil => rfl
  | cons x V ih => exact ih _

private theorem circuit_congr {V : List (X m n)} {f g : X m n → Op (Fin 2 × Fin 2)}
    (h : ∀ x ∈ V, f x = g x) : circuit V f = circuit V g := by
  induction V with
  | nil => rfl
  | cons x V ih => simp only [circuit, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem circuit_site_expansion {K : Type} [Fintype K] (V : List (X m n)) (hd : V.Nodup)
    (x : X m n) (hx : x ∈ V) (f : X m n → Op (Fin 2 × Fin 2)) (g : K → Op (Fin 2 × Fin 2))
    (c : K → ℝ) (h : f x = ∑ k, c k • g k) (A : GlobalMat m n) :
    circuit V f A = ∑ k, c k • circuit V (Function.update f x (g k)) A := by
  classical
  induction V generalizing A with
  | nil => simp at hx
  | cons y V ih =>
    have hno := (List.nodup_cons.mp hd).1
    by_cases he : y = x
    · subst y
      have hg (k) : circuit V (Function.update f x (g k)) = circuit V f :=
        circuit_congr fun z hz => Function.update_of_ne (show z ≠ x from fun hh => hno (hh ▸ hz)) _ _
      simp only [circuit, LinearMap.comp_apply, Function.update_self, hg]
      have hh : embed x (∑ k, c k • g k) A = ∑ k, c k • embed x (g k) A := by
        apply Matrix.ext
        intro a b
        simp [embed, LinearMap.sum_apply, Matrix.sum_apply]
      rw [h,hh,map_sum]
      simp only [LinearMap.map_smul_of_tower]
    · have hmem := (List.mem_cons.mp hx).resolve_left (Ne.symm he)
      simpa only [circuit, LinearMap.comp_apply, Function.update_of_ne he] using
        ih (List.nodup_cons.mp hd).2 hmem (embed y (f y) A)


open HardyCausaloid
private theorem label_basis_coordinates (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (x : X m n) (p : Ω × Ω) :
    elemCoeff S (labelOp (L x p)) = Pi.single p 1 := by
  classical
  have h := (eq20_two_qubit_expansion S).1 _ ((L x p).1.cp (L x p).2)
  symm
  apply ((eq20_two_qubit_expansion S).2 _ h).2
  simp [Pi.single_apply]
  exact hL x p

private theorem labels_injective (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (x : X m n) : Function.Injective (L x) := by
  intro p p' h
  have hv := (label_basis_coordinates S L hL x p).symm.trans
    ((congrArg (fun α => elemCoeff S (labelOp α)) h).trans (label_basis_coordinates S L hL x p'))
  by_contra hp
  simpa [Pi.single_apply, hp, Ne.symm hp] using congrFun hv p

open Classical in
private noncomputable def labelEquiv (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (x : X m n) : Ω × Ω ≃ omegaOne L x :=
  Equiv.ofBijective (fun p => ⟨L x p, Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩) ⟨
    fun _ _ h => labels_injective S L hL x (congrArg Subtype.val h), by
      rintro ⟨l,hl⟩
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨p,rfl⟩⟩

private theorem vertex_grid_expansion {m n : ℕ} (ρ : GlobalMat m n) (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (t : ∀ x, Label (Setting m n) (Outcome m n) x) (x : X m n) :
    latticeProb ρ t = ∑ k : omegaOne L x,
      elemCoeff S (labelOp (t x)) (decode L x k.val) * latticeProb ρ (Function.update t x k.val) := by
  classical
  let V := vertexList m n
  let op (z : X m n) := labelOp (t z)
  let c := elemCoeff S (op x)
  let B (p : Ω × Ω) := prodOp (S.map p.1) (S.map p.2)
  have hx : op x = ∑ p, c p • B p :=
    ((eq20_two_qubit_expansion S).2 _ ((eq20_two_qubit_expansion S).1 _ ((t x).1.cp (t x).2))).1
  have hv : V.Nodup := (List.nodup_finRange m).product (List.nodup_finRange n)
  have mem : x ∈ V := by rcases x with ⟨i,j⟩; simp [V,vertexList,List.product,List.mem_flatMap]
  have hh := circuit_site_expansion V hv x mem op B c hx ρ
  let e := labelEquiv S L hL x
  rw [← e.sum_comp]
  have coord (p : Ω × Ω) : decode L x (e p).val = p :=
    Function.leftInverse_invFun (labels_injective S L hL x) p
  have hchange (p : Ω × Ω) : Function.update op x (B p) =
      fun z => labelOp (Function.update t x (e p).val z) := by
    funext z
    by_cases he : z = x
    · subst z; simp only [Function.update_self]; exact (hL x p).symm
    · simp [Function.update_of_ne he,op]
  have ht := congrArg (fun M => (Matrix.trace M).re) hh
  simpa only [circuit_fold, hchange, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,sub_zero,
    latticeProb, evolve, coord, op, c, V] using ht


end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {m n : ℕ} (ρ : GlobalMat m n)
    (M : Model (Setting m n) (Outcome m n)) (hM : IsLatticeModel ρ M)
    (S : FiducialFamily) (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (hL : IsFiducialLabels S L) (O : Finset (X m n))
    (α : Lab (Setting m n) (Outcome m n) O) (s : ∀ x, Label (Setting m n) (Outcome m n) x) :
    regionTable M O α s = ∑ l : ∀ x : O, omegaOne L x.val,
      (∏ x : O, elemCoeff S (labelOp (α x)) (decode L x.val (l x).val)) *
        regionTable M O (fun x => (l x).val) s := by
  classical
  have prob (t : ∀ x, Label (Setting m n) (Outcome m n) x) : M.P t = latticeProb ρ t :=
    hM (fun x => (t x).1) (fun x => (t x).2)
  apply HardyCausaloid.product_reconstruction (fun i : O => omegaOne L i.val)
    (fun i t k => elemCoeff S (labelOp t) (decode L i.val k.val)) (fun t => regionTable M O t s) _ _ α
  · intro t i
    let a := glue O t s
    have update (k : omegaOne L i.val) : glue O (Function.update t i k.val) s =
        Function.update a i.val k.val := by
      funext x
      by_cases he : x = i.val
      · subst x; simp [glue, i.property]
      · by_cases hx : x ∈ O
        · have hn : (⟨x,hx⟩ : O) ≠ i := fun h => he (congrArg Subtype.val h)
          simp [a,glue,hx,Function.update_of_ne he,Function.update_of_ne hn]
        · simp [a,glue,hx,Function.update_of_ne he]
    simp only [regionTable,prob,update]
    have hi : a i.val = t i := by simp [a,glue,i.property]
    simpa only [hi] using vertex_grid_expansion ρ S L hL a i.val
  · intro i k j
    let e := labelEquiv S L hL i.val
    obtain ⟨k,rfl⟩ := e.surjective k
    obtain ⟨j,rfl⟩ := e.surjective j
    have hd : decode L i.val (e j).val = j := Function.leftInverse_invFun (labels_injective S L hL i.val) j
    change elemCoeff S (labelOp (L i.val k)) _ = _
    rw [label_basis_coordinates S L hL,hd]
    by_cases h : k = j <;> simp [h,Ne.symm,e.injective.eq_iff]

