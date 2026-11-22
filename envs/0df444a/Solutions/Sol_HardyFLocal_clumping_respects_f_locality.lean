-- Prove2me | solution 1 for HardyFLocal.clumping_respects_f_locality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:26:27.778796+00:00
-- url     : https://prove2.me/submissions/93d5399a-9414-4316-8dea-20ea34be06ef

import Definitions.Def_HardyFLocal_ClumpCausaloid

namespace HardyFLocal
open HardyCausaloid
variable {m n : ℕ}

private theorem wire_sequential (q : Q m n) :
    (qubitVertices q).IsChain IsSequentialPair := by
  cases q <;> simp [qubitVertices, List.isChain_iff_getElem, IsSequentialPair]

private theorem split_preserves_chain {α : Type*} (R : α → α → Prop) (p : α → Bool)
    (xs acc : List α) (whole : (acc.reverse ++ xs).IsChain R)
    (good : ∀ x ∈ acc, p x = false) (c : List α) (hc : c ∈ xs.splitOnPPrepend p acc) :
    c.IsChain R ∧ ∀ x ∈ c, p x = false := by
  induction xs generalizing acc with
  | nil => simp_all
  | cons x xs ih =>
    cases hp : p x with
    | false =>
      exact ih (x :: acc) (by simpa using whole) (List.forall_mem_cons.mpr ⟨hp, good⟩)
        (by simpa only [List.splitOnPPrepend_cons_neg hp] using hc)
    | true =>
      rcases List.mem_cons.mp (List.splitOnPPrepend_cons_pos hp ▸ hc) with rfl | htail
      · exact ⟨whole.left_of_append, by simpa using good⟩
      · exact ih [] (by simpa using whole.right_of_append.tail) (by simp) htail

private theorem chain_congr_on_wire {V : Type} (T T' : V → V → PairTable)
    (label : V → Ω) (xs : List V)
    (agree : xs.IsChain (fun x y => T x y = T' x y)) :
    chain T (xs.map fun x => (x, label x)) = chain T' (xs.map fun x => (x, label x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      exact funext fun k => Finset.sum_congr rfl fun j _ =>
        congrArg₂ (· * ·) (congrFun (ih (List.isChain_cons_cons.mp agree).2) j)
          (congrArg (fun t : PairTable => t j (label x) k) (List.isChain_cons_cons.mp agree).1)

private theorem clump_local {O : Finset (X m n)} (q : Q m n) (c : List (X m n))
    (hc : c ∈ clumps O q) {T T' : X m n → X m n → PairTable}
    (hT : ∀ x ∈ O, ∀ y ∈ O, IsSequentialPair x y → T x y = T' x y)
    (a b : X m n → Ω × Ω) : clumpFactor T q c a b = clumpFactor T' q c a b := by
  obtain ⟨seq, inside⟩ := split_preserves_chain IsSequentialPair (fun x => decide (x ∉ O))
    (qubitVertices q) [] (by simpa using wire_sequential q) (by simp) c (List.mem_filter.mp hc).1
  have agree := seq.imp_of_mem_imp (fun x y hx hy hxy =>
    hT x (by simpa using inside x hx) y (by simpa using inside y hy) hxy)
  cases c with
  | nil => rfl
  | cons x xs =>
    exact congrFun (chain_congr_on_wire T T' (fun y => onQubit q (a y)) (x :: xs) agree)
      (onQubit q (b x))

end HardyFLocal

open HardyCausaloid HardyFLocal

theorem solution {m n : ℕ}
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (T T' : X m n → X m n → PairTable)
    (E E' : ∀ x : X m n, Label (Setting m n) (Outcome m n) x → Ω × Ω → ℝ)
    (O : Finset (X m n))
    (hT : ∀ x ∈ O, ∀ x' ∈ O, IsSequentialPair x x' → T x x' = T' x x')
    (hE : ∀ x ∈ O, E x = E' x) :
    (clumpCausaloid L T E).ΩC O = (clumpCausaloid L T' E').ΩC O ∧
    (∀ (l : ∀ x : O, omegaOne L x.1) (k : omegaC L O),
      (clumpCausaloid L T E).Λ O l k = (clumpCausaloid L T' E').Λ O l k) ∧
    ∀ α : Lab (Setting m n) (Outcome m n) O,
      (clumpCausaloid L T E).r O α = (clumpCausaloid L T' E').r O α := by
  have lam (l : ∀ x : O, omegaOne L x.val) (k : omegaC L O) :
      (clumpCausaloid L T E).Λ O l k = (clumpCausaloid L T' E').Λ O l k :=
    Finset.prod_congr (s₁ := Finset.univ) rfl fun q _ => congrArg List.prod
      (List.map_congr_left fun c hc => clump_local q c hc hT (famPairs L O l) (famPairs L O k.val))
  refine ⟨rfl, lam, fun α => funext fun k => Finset.sum_congr rfl fun l _ => ?_⟩
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun x _ =>
    congrFun (congrFun (hE x.val x.property) (α x)) (decode L x.val (l x).val)) (lam l k)
