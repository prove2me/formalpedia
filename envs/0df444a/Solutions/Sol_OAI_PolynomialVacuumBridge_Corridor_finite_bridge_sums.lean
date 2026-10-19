-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:27:27.130632+00:00
-- url     : https://prove2.me/submissions/2581a17e-5420-47dc-8695-32b4672e7156

import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def neighbor (v : Vertex) (k : Fin 3) : Vertex :=
  match v with
  | .up i j => if k = 0 then .down i (j - 1)
      else if k = 1 then .down i j else .down (i - 1) j
  | .down i j => if k = 0 then .up i (j + 1)
      else if k = 1 then .up i j else .up (i + 1) j

abbrev Germ := Vertex × Fin 3

def outgoingSlot (g : Germ) (b : Bool) : Fin 3 :=
  g.2 + (if b then 2 else 1)

def advance (g : Germ) (b : Bool) : Germ :=
  (neighbor g.1 (outgoingSlot g b), outgoingSlot g b)

def Stopped : Finset Vertex → Germ → List Bool → Prop
  | D, g, [] => g.1 ∉ D
  | D, g, b :: w => g.1 ∈ D ∧ Stopped (D.erase g.1) (advance g b) w

def leaves (D : Finset Vertex) (g : Germ) : Finset (List Bool) :=
  if g.1 ∈ D then
    ((leaves (D.erase g.1) (advance g true)).image (List.cons true)) ∪
    ((leaves (D.erase g.1) (advance g false)).image (List.cons false))
  else {[]}
termination_by D.card
decreasing_by all_goals exact Finset.card_erase_lt_of_mem (by assumption)

noncomputable def turnAngle (b : Bool) : ℝ :=
  if b then Real.pi / 3 else -(Real.pi / 3)

noncomputable def stepWeight (b : Bool) : ℂ :=
  (criticalActivity : ℂ) * Complex.exp (((3 / 8 : ℝ) * turnAngle b : ℝ) * Complex.I)

noncomputable def wordWeight (w : List Bool) : ℂ := (w.map stepWeight).prod

def traced : Germ → List Bool → List Vertex
  | _, [] => []
  | g, b :: w => g.1 :: traced (advance g b) w

def terminalGerm : Germ → List Bool → Germ
  | g, [] => g
  | g, b :: w => terminalGerm (advance g b) w

noncomputable def explorationTotal (D : Finset Vertex) (v : Vertex) : ℂ :=
  ∑ k : Fin 3, ∑ w ∈ leaves (D.erase v) (neighbor v k, k), wordWeight w

@[simp] theorem neighbor_neighbor (v : Vertex) (k : Fin 3) :
    neighbor (neighbor v k) k = v := by
  cases v <;> fin_cases k <;> simp [neighbor]

theorem adjacent_neighbor (v : Vertex) (k : Fin 3) : adjacent v (neighbor v k) := by
  cases v <;> fin_cases k <;> simp [neighbor, adjacent]

theorem neighbor_injective (v : Vertex) : Function.Injective (neighbor v) := by
  intro a b hab
  cases v <;> fin_cases a <;> fin_cases b <;> simp_all [neighbor] <;> omega

@[simp] theorem advance_adjacent (g : Germ) (b : Bool) :
    adjacent g.1 (advance g b).1 := adjacent_neighbor _ _

theorem advance_not_backtracking (g : Germ) (b : Bool) :
    (advance g b).1 ≠ neighbor g.1 g.2 := by
  intro heq
  have hk := neighbor_injective g.1 heq
  obtain ⟨v, k⟩ := g
  fin_cases k <;> cases b <;> simp [outgoingSlot] at hk

@[simp] theorem wordWeight_nil : wordWeight [] = 1 := rfl
@[simp] theorem wordWeight_cons (b : Bool) (w : List Bool) :
    wordWeight (b :: w) = stepWeight b * wordWeight w := rfl

theorem critical_cos_pos : 0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

theorem stepWeight_sum : stepWeight true + stepWeight false = 1 := by
  have hc : Real.cos (Real.pi / 8) ≠ 0 := ne_of_gt critical_cos_pos
  simp only [stepWeight, turnAngle, Bool.false_eq_true, ite_false, ite_true]
  have ht : (3 / 8 : ℝ) * (Real.pi / 3) = Real.pi / 8 := by ring
  have hf : (3 / 8 : ℝ) * -(Real.pi / 3) = -(Real.pi / 8) := by ring
  rw [ht, hf, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  calc
    _ = ((criticalActivity * (2 * Real.cos (Real.pi / 8)) : ℝ) : ℂ) := by
      push_cast
      ring
    _ = 1 := by
      have hw : criticalActivity * (2 * Real.cos (Real.pi / 8)) = 1 :=
        inv_mul_cancel₀ (mul_ne_zero (by norm_num) hc)
      rw [hw]
      norm_num

theorem mem_leaves_iff (D : Finset Vertex) (g : Germ) (w : List Bool) :
    w ∈ leaves D g ↔ Stopped D g w := by
  induction w generalizing D g with
  | nil =>
      rw [leaves]
      by_cases h : g.1 ∈ D <;> simp [h, Stopped]
  | cons b w ih =>
      rw [leaves]
      by_cases h : g.1 ∈ D
      · cases b <;> simp [h, Stopped, ih]
      · simp [h, Stopped]

theorem stopped_traced (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : Stopped D g w) :
    (traced g w).Nodup ∧ ∀ v ∈ traced g w, v ∈ D := by
  induction w generalizing D g with
  | nil => simp [traced]
  | cons b w ih =>
      obtain ⟨hg, hw⟩ := hw
      obtain ⟨hn, hD⟩ := ih (D.erase g.1) (advance g b) hw
      constructor
      · simp only [traced, List.nodup_cons]
        refine ⟨?_, hn⟩
        intro hmem
        exact (Finset.mem_erase.mp (hD g.1 hmem)).1 rfl
      · intro v hv
        simp only [traced, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hg
        · exact (Finset.mem_erase.mp (hD v hv)).2

theorem traced_length (g : Germ) (w : List Bool) : (traced g w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [traced, List.length_cons, ih]

theorem trace_chain (g : Germ) (w : List Bool) :
    (traced g w ++ [(terminalGerm g w).1]).IsChain adjacent := by
  induction w generalizing g with
  | nil => simp [traced, terminalGerm]
  | cons b w ih =>
      simp only [traced, List.cons_append, terminalGerm]
      apply List.IsChain.cons (ih (advance g b))
      cases w with
      | nil => simp [traced, terminalGerm, advance_adjacent]
      | cons c w => simp [traced, terminalGerm, advance_adjacent]

theorem wordWeight_physical (w : List Bool) :
    wordWeight w = (criticalActivity : ℂ) ^ w.length *
      Complex.exp (((3 / 8 : ℝ) * (w.map turnAngle).sum : ℝ) * Complex.I) := by
  induction w with
  | nil => simp [wordWeight]
  | cons b w ih =>
      simp only [wordWeight_cons, ih, List.length_cons, List.map_cons, List.sum_cons]
      simp only [stepWeight, mul_add, Complex.ofReal_add, Complex.ofReal_mul]
      rw [add_mul, Complex.exp_add, pow_succ]
      ring

theorem sum_cons_image (s : Finset (List Bool)) (b : Bool) :
    ∑ w ∈ s.image (List.cons b), wordWeight w =
      stepWeight b * ∑ w ∈ s, wordWeight w := by
  rw [Finset.sum_image]
  · simp only [wordWeight_cons, Finset.mul_sum]
  · intro a ha c hc hac
    exact List.cons.inj hac |>.2

theorem disjoint_cons_images (s t : Finset (List Bool)) :
    Disjoint (s.image (List.cons true)) (t.image (List.cons false)) := by
  apply Finset.disjoint_left.mpr
  intro w hs ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp ht
  exact Bool.false_ne_true (List.cons.inj heq).1

theorem leaf_balance (D : Finset Vertex) (g : Germ) :
    ∑ w ∈ leaves D g, wordWeight w = 1 := by
  induction D using Finset.strongInductionOn generalizing g with
  | _ D ih =>
      rw [leaves]
      by_cases hg : g.1 ∈ D
      · simp only [hg, ite_true]
        rw [Finset.sum_union (disjoint_cons_images _ _), sum_cons_image, sum_cons_image]
        have hers : D.erase g.1 ⊂ D := Finset.erase_ssubset hg
        rw [ih _ hers _, ih _ hers _]
        simpa only [mul_one] using stepWeight_sum
      · simp [hg]

theorem visit_exploration_balance (D : Finset Vertex) (v : Vertex) (_hv : v ∈ D) :
    explorationTotal D v = 3 := by
  simp [explorationTotal, leaf_balance]

noncomputable def complexPosition (v : Vertex) : ℂ :=
  (position v).1 + (position v).2 * Complex.I

theorem exp_turnAngle (b : Bool) :
    Complex.exp ((turnAngle b : ℝ) * Complex.I) =
      (1 / 2 : ℂ) + (if b then 1 else -1) * (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  cases b <;> simp only [turnAngle, Bool.false_eq_true, ite_false, ite_true] <;>
    rw [Complex.exp_ofReal_mul_I] <;>
    simp [Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring

theorem advance_rotation (g : Germ) (b : Bool) :
    complexPosition (advance g b).1 - complexPosition g.1 =
      Complex.exp ((turnAngle b : ℝ) * Complex.I) *
        (complexPosition g.1 - complexPosition (neighbor g.1 g.2)) := by
  rw [exp_turnAngle]
  obtain ⟨v, k⟩ := g
  have hsq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  cases v <;> fin_cases k <;> cases b <;>
    simp [advance, outgoingSlot, neighbor, complexPosition, position] <;>
    ring_nf <;> simp [hsq] <;> ring

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def reverseGerm (g : Germ) : Germ := (neighbor g.1 g.2, g.2)

def reverseTurns (w : List Bool) : List Bool := w.reverse.map Bool.not

@[simp] theorem reverseGerm_reverseGerm (g : Germ) :
    reverseGerm (reverseGerm g) = g := by
  rcases g with ⟨v,k⟩
  simp [reverseGerm]

@[simp] theorem reverseTurns_reverseTurns (w : List Bool) :
    reverseTurns (reverseTurns w) = w := by
  simp [reverseTurns, List.map_reverse, List.map_map, Function.comp_def]

@[simp] theorem reverseTurns_nil : reverseTurns [] = [] := rfl

@[simp] theorem reverseTurns_cons (b : Bool) (w : List Bool) :
    reverseTurns (b :: w) = reverseTurns w ++ [!b] := by
  simp [reverseTurns]

@[simp] theorem terminalGerm_append (g : Germ) (u w : List Bool) :
    terminalGerm g (u ++ w) = terminalGerm (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih => simpa [terminalGerm] using ih (advance g b)

@[simp] theorem traced_append (g : Germ) (u w : List Bool) :
    traced g (u ++ w) = traced g u ++ traced (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih => simp [traced, terminalGerm, ih]

@[simp] theorem advance_reverse (g : Germ) (b : Bool) :
    advance (reverseGerm (advance g b)) (!b) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [advance, outgoingSlot, reverseGerm]

@[simp] theorem terminalGerm_reverse (g : Germ) (w : List Bool) :
    terminalGerm (reverseGerm (terminalGerm g w)) (reverseTurns w) = reverseGerm g := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    rw [reverseTurns_cons, terminalGerm_append]
    simp only [terminalGerm, ih, advance_reverse]

@[simp] theorem traced_reverse (g : Germ) (w : List Bool) :
    traced (reverseGerm (terminalGerm g w)) (reverseTurns w) = (traced g w).reverse := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    rw [reverseTurns_cons, traced_append]
    simp only [terminalGerm, ih, terminalGerm_reverse, traced, List.reverse_cons]
    simp [reverseGerm, advance]

@[simp] theorem stepWeight_not (b : Bool) :
    stepWeight (!b) = (starRingEnd ℂ) (stepWeight b) := by
  have ha : turnAngle (!b) = -turnAngle b := by cases b <;> simp [turnAngle]
  rw [stepWeight, ha, stepWeight, map_mul, ← Complex.exp_conj]
  simp only [Complex.conj_ofReal, map_mul, Complex.conj_I]
  congr 1
  push_cast
  ring_nf

@[simp] theorem wordWeight_reverse (w : List Bool) :
    wordWeight (reverseTurns w) = (starRingEnd ℂ) (wordWeight w) := by
  unfold wordWeight reverseTurns
  rw [List.map_map]
  simp only [Function.comp_def, stepWeight_not]
  rw [show (fun b => (starRingEnd ℂ) (stepWeight b)) =
    (starRingEnd ℂ) ∘ stepWeight from rfl, ← List.map_map, map_list_prod]
  simp only [List.map_reverse, List.prod_reverse]

theorem stopped_of_trace (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hD : ∀ v ∈ traced g w, v ∈ D)
    (ht : (terminalGerm g w).1 ∉ D) : Stopped D g w := by
  induction w generalizing D g with
  | nil => exact ht
  | cons b w ih =>
    simp only [traced, List.nodup_cons] at hN
    refine ⟨hD _ (by simp [traced]), ih _ _ hN.2 ?_ ?_⟩
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun he => hN.1 (he ▸ hv),
        hD _ (by simp [traced, hv])⟩
    · exact fun hm => ht (Finset.mem_of_mem_erase hm)

def IsExcursion (D : Finset Vertex) (e : Germ × List Bool) : Prop :=
  e.1.1 ∈ D ∧ (reverseGerm e.1).1 ∉ D ∧ Stopped D e.1 e.2 ∧
    (terminalGerm e.1 e.2).1 ∉ D

noncomputable def excursions (D : Finset Vertex) : Finset (Germ × List Bool) := by
  classical
  exact ((D.product Finset.univ).biUnion fun g =>
    (leaves D g).image fun w => (g, w)).filter (IsExcursion D)

@[simp] theorem mem_excursions (D : Finset Vertex) (e : Germ × List Bool) :
    e ∈ excursions D ↔ IsExcursion D e := by
  classical
  rw [excursions, Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_, he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨e.1, Finset.mem_product.mpr ⟨he.1, Finset.mem_univ _⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨e.2, (mem_leaves_iff _ _ _).mpr he.2.2.1, rfl⟩

def reverseExcursion (e : Germ × List Bool) : Germ × List Bool :=
  (reverseGerm (terminalGerm e.1 e.2), reverseTurns e.2)

@[simp] theorem reverseExcursion_reverseExcursion (e : Germ × List Bool) :
    reverseExcursion (reverseExcursion e) = e := by
  rcases e with ⟨g,w⟩
  simp [reverseExcursion]

theorem IsExcursion.nonempty {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : e.2 ≠ [] := by
  intro hw
  exact he.2.2.2 (by simpa [hw, terminalGerm] using he.1)

theorem reverse_first_mem (g : Germ) (w : List Bool) (hw : w ≠ []) :
    (reverseGerm (terminalGerm g w)).1 ∈ traced g w := by
  have hr : reverseTurns w ≠ [] := by
    intro he
    have := congrArg reverseTurns he
    exact hw (by simpa using this)
  obtain ⟨b,u,hu⟩ := List.exists_cons_of_ne_nil hr
  have hm : (reverseGerm (terminalGerm g w)).1 ∈
      traced (reverseGerm (terminalGerm g w)) (reverseTurns w) := by
    simp [hu, traced]
  simpa using hm

theorem IsExcursion.reverse {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : IsExcursion D (reverseExcursion e) := by
  obtain ⟨hN,hD⟩ := stopped_traced D e.1 e.2 he.2.2.1
  refine ⟨hD _ (reverse_first_mem _ _ he.nonempty), ?_, ?_, ?_⟩
  · simpa [reverseExcursion] using he.2.2.2
  · apply stopped_of_trace
    · simpa [reverseExcursion] using hN
    · intro v hv
      apply hD v
      simpa [reverseExcursion] using hv
    · simpa [reverseExcursion] using he.2.1
  · simpa [reverseExcursion] using he.2.1

@[simp] theorem reverseExcursion_mem (D : Finset Vertex) (e : Germ × List Bool) :
    reverseExcursion e ∈ excursions D ↔ e ∈ excursions D := by
  rw [mem_excursions, mem_excursions]
  exact ⟨fun he => by simpa using he.reverse, IsExcursion.reverse⟩

noncomputable def visitSum (D : Finset Vertex) (v : Vertex) : ℂ := by
  classical
  exact ∑ e ∈ excursions D, if v ∈ traced e.1 e.2 then wordWeight e.2 else 0

theorem visitSum_conj (D : Finset Vertex) (v : Vertex) :
    (starRingEnd ℂ) (visitSum D v) = visitSum D v := by
  classical
  simp only [visitSum, map_sum]
  simp_rw [apply_ite (starRingEnd ℂ), map_zero]
  apply Finset.sum_bij (fun e _ => reverseExcursion e)
  · intro e he
    exact (reverseExcursion_mem D e).mpr he
  · intro e he f hf hef
    have := congrArg reverseExcursion hef
    simpa using this
  · intro e he
    exact ⟨reverseExcursion e, (reverseExcursion_mem D e).mpr he, by simp⟩
  · intro e he
    simp [reverseExcursion]

theorem visitSum_im (D : Finset Vertex) (v : Vertex) : (visitSum D v).im = 0 :=
  Complex.conj_eq_iff_im.mp (visitSum_conj D v)

noncomputable def markedLeaves (D : Finset Vertex) (g : Germ) (v : Vertex) : ℂ := by
  classical
  exact ∑ w ∈ leaves D g, if v ∈ traced g w then wordWeight w else 0

noncomputable def firstArrival (D : Finset Vertex) (g : Germ) (v : Vertex) : ℂ := by
  classical
  exact ∑ w ∈ leaves (D.erase v) g,
    if (terminalGerm g w).1 = v then wordWeight w else 0

theorem sum_leaves_of_mem (D : Finset Vertex) (g : Germ) (hg : g.1 ∈ D)
    (f : List Bool → ℂ) :
    ∑ w ∈ leaves D g, f w =
      (∑ w ∈ leaves (D.erase g.1) (advance g true), f (true :: w)) +
      (∑ w ∈ leaves (D.erase g.1) (advance g false), f (false :: w)) := by
  rw [leaves, ite_eq_left hg, Finset.sum_union (disjoint_cons_images _ _)]
  congr 1 <;> apply Finset.sum_image <;> intro a ha b hb hab <;>
    exact (List.cons.inj hab).2

theorem leaves_of_not_mem (D : Finset Vertex) (g : Germ) (hg : g.1 ∉ D) :
    leaves D g = {[]} := by rw [leaves, ite_eq_right hg]

theorem markedLeaves_eq_firstArrival (D : Finset Vertex) (g : Germ) (v : Vertex)
    (hv : v ∈ D) : markedLeaves D g v = firstArrival D g v := by
  classical
  induction D using Finset.strongInductionOn generalizing g with
  | _ D ih =>
      by_cases hgv : g.1 = v
      · have hg : g.1 ∈ D := hgv ▸ hv
        have hm : markedLeaves D g v = 1 := by
          unfold markedLeaves
          convert leaf_balance D g using 1
          apply Finset.sum_congr rfl
          intro w hw
          have hne : w ≠ [] := by
            intro he
            subst w
            have := (mem_leaves_iff D g []).mp hw
            exact this hg
          obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hne
          simp [traced, hgv]
        rw [hm]
        simp [firstArrival, leaves_of_not_mem (D.erase v) g (by simp [hgv]), terminalGerm, hgv]
      · by_cases hg : g.1 ∈ D
        · have hers : D.erase g.1 ⊂ D := Finset.erase_ssubset hg
          have hve : v ∈ D.erase g.1 := Finset.mem_erase.mpr ⟨Ne.symm hgv, hv⟩
          have hge : g.1 ∈ D.erase v := Finset.mem_erase.mpr ⟨hgv,hg⟩
          unfold markedLeaves firstArrival
          rw [sum_leaves_of_mem _ _ hg, sum_leaves_of_mem _ _ hge]
          simp +instances only [traced, List.mem_cons, eq_comm (a := v), hgv, false_or,
            terminalGerm, wordWeight_cons, ← mul_ite_zero, ← Finset.mul_sum]
          rw [Finset.erase_right_comm (a := v) (b := g.1)]
          change _ =
            (∑ w ∈ leaves ((D.erase g.1).erase v) (advance g true),
              if (terminalGerm (advance g true) w).1 = v then
                stepWeight true * wordWeight w else 0) +
            (∑ w ∈ leaves ((D.erase g.1).erase v) (advance g false),
              if (terminalGerm (advance g false) w).1 = v then
                stepWeight false * wordWeight w else 0)
          simp_rw [← mul_ite_zero, ← Finset.mul_sum]
          change stepWeight true * markedLeaves (D.erase g.1) (advance g true) v +
            stepWeight false * markedLeaves (D.erase g.1) (advance g false) v =
            stepWeight true * firstArrival (D.erase g.1) (advance g true) v +
            stepWeight false * firstArrival (D.erase g.1) (advance g false) v
          rw [ih _ hers _ hve, ih _ hers _ hve]
        · have hge : g.1 ∉ D.erase v := fun h => hg (Finset.mem_of_mem_erase h)
          simp [markedLeaves, firstArrival, leaves_of_not_mem _ _ hg,
            leaves_of_not_mem _ _ hge, traced, terminalGerm, hgv]

noncomputable def exitSum (D : Finset Vertex) (g : Germ) : ℂ := by
  classical
  exact ∑ w ∈ leaves D g, if (terminalGerm g w).1 ∉ D then wordWeight w else 0

noncomputable def collisionSum (D : Finset Vertex) (g : Germ) : ℂ := by
  classical
  exact ∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D then wordWeight w else 0

theorem exit_add_collision (D : Finset Vertex) (g : Germ) :
    exitSum D g + collisionSum D g = 1 := by
  classical
  unfold exitSum collisionSum
  rw [← Finset.sum_add_distrib]
  convert leaf_balance D g using 1
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ht : (terminalGerm g w).1 ∈ D <;> simp [ht]

noncomputable def boundaryGerms (D : Finset Vertex) : Finset Germ := by
  classical
  exact (D.product Finset.univ).filter fun g => (reverseGerm g).1 ∉ D

@[simp] theorem mem_boundaryGerms (D : Finset Vertex) (g : Germ) :
    g ∈ boundaryGerms D ↔ g.1 ∈ D ∧ (reverseGerm g).1 ∉ D := by
  classical
  simp [boundaryGerms]

noncomputable def firstArrivals (D : Finset Vertex) (v : Vertex) :
    Finset (Germ × List Bool) := by
  classical
  exact ((boundaryGerms D).biUnion fun g =>
    (leaves (D.erase v) g).image fun w => (g,w)).filter fun e =>
      (terminalGerm e.1 e.2).1 = v

@[simp] theorem mem_firstArrivals (D : Finset Vertex) (v : Vertex)
    (e : Germ × List Bool) : e ∈ firstArrivals D v ↔
    e.1 ∈ boundaryGerms D ∧ Stopped (D.erase v) e.1 e.2 ∧
      (terminalGerm e.1 e.2).1 = v := by
  classical
  simp only [firstArrivals, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨g,hg,w,hw,he⟩,ht⟩
    subst e
    exact ⟨hg, (mem_leaves_iff _ _ _).mp hw,ht⟩
  · rintro ⟨hg,hw,ht⟩
    exact ⟨⟨e.1,hg,e.2,(mem_leaves_iff _ _ _).mpr hw,rfl⟩,ht⟩

noncomputable def rayExits (D : Finset Vertex) (v : Vertex) :
    Finset (Fin 3 × List Bool) := by
  classical
  exact (Finset.univ.biUnion fun k : Fin 3 =>
    (leaves (D.erase v) (neighbor v k,k)).image fun w => (k,w)).filter fun e =>
      (terminalGerm (neighbor v e.1,e.1) e.2).1 ∉ D

@[simp] theorem mem_rayExits (D : Finset Vertex) (v : Vertex)
    (e : Fin 3 × List Bool) : e ∈ rayExits D v ↔
    Stopped (D.erase v) (neighbor v e.1,e.1) e.2 ∧
      (terminalGerm (neighbor v e.1,e.1) e.2).1 ∉ D := by
  classical
  simp only [rayExits, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨k,hk,w,hw,he⟩,ht⟩
    subst e
    exact ⟨(mem_leaves_iff _ _ _).mp hw,ht⟩
  · rintro ⟨hw,ht⟩
    exact ⟨⟨e.1,Finset.mem_univ _,e.2,(mem_leaves_iff _ _ _).mpr hw,rfl⟩,ht⟩

def reversePrefix (e : Germ × List Bool) : Fin 3 × List Bool :=
  ((terminalGerm e.1 e.2).2, reverseTurns e.2)

def reverseRay (v : Vertex) (e : Fin 3 × List Bool) : Germ × List Bool :=
  (reverseGerm (terminalGerm (neighbor v e.1,e.1) e.2), reverseTurns e.2)

theorem reversePrefix_initial {v : Vertex} {e : Germ × List Bool}
    (ht : (terminalGerm e.1 e.2).1 = v) :
    (neighbor v (reversePrefix e).1,(reversePrefix e).1) =
      reverseGerm (terminalGerm e.1 e.2) := by
  simp [reversePrefix,reverseGerm,ht]

theorem reversePrefix_mem {D : Finset Vertex} {v : Vertex}
    {e : Germ × List Bool} (he : e ∈ firstArrivals D v) :
    reversePrefix e ∈ rayExits D v := by
  classical
  obtain ⟨hg,hs,ht⟩ := (mem_firstArrivals D v e).mp he
  obtain ⟨hgD,hgb⟩ := (mem_boundaryGerms D e.1).mp hg
  obtain ⟨hN,hD⟩ := stopped_traced _ _ _ hs
  rw [mem_rayExits,reversePrefix_initial ht]
  constructor
  · apply stopped_of_trace
    · simpa [reversePrefix] using hN
    · intro u hu
      apply hD u
      simpa [reversePrefix] using hu
    · simpa [reversePrefix] using
        (fun hu => hgb (Finset.mem_of_mem_erase hu) : (reverseGerm e.1).1 ∉ D.erase v)
  · simpa [reversePrefix] using hgb

theorem reverseRay_mem {D : Finset Vertex} {v : Vertex} (hv : v ∈ D)
    {e : Fin 3 × List Bool} (he : e ∈ rayExits D v) :
    reverseRay v e ∈ firstArrivals D v := by
  classical
  obtain ⟨hs,ht⟩ := (mem_rayExits D v e).mp he
  obtain ⟨hN,hD⟩ := stopped_traced _ _ _ hs
  rw [mem_firstArrivals,mem_boundaryGerms]
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · by_cases hw : e.2 = []
    · simpa [reverseRay,hw,terminalGerm,reverseGerm] using hv
    · exact Finset.mem_of_mem_erase
        (hD _ (reverse_first_mem (neighbor v e.1,e.1) e.2 hw))
  · simpa [reverseRay] using ht
  · apply stopped_of_trace
    · simpa [reverseRay] using hN
    · intro u hu
      apply hD u
      simpa [reverseRay] using hu
    · simp only [reverseRay, terminalGerm_reverse]
      simp [reverseGerm]
  · simp only [reverseRay, terminalGerm_reverse]
    simp [reverseGerm]

@[simp] theorem reversePrefix_reverseRay (v : Vertex) (e : Fin 3 × List Bool) :
    reversePrefix (reverseRay v e) = e := by
  simp only [reversePrefix,reverseRay, terminalGerm_reverse,
    reverseTurns_reverseTurns]
  rfl

theorem reverseRay_reversePrefix (v : Vertex) (e : Germ × List Bool)
    (ht : (terminalGerm e.1 e.2).1 = v) : reverseRay v (reversePrefix e) = e := by
  unfold reverseRay
  rw [reversePrefix_initial ht]
  simp [reversePrefix]

theorem prefix_ray_reversal (D : Finset Vertex) (v : Vertex) (hv : v ∈ D) :
    (∑ e ∈ firstArrivals D v, wordWeight e.2) =
      (starRingEnd ℂ) (∑ e ∈ rayExits D v, wordWeight e.2) := by
  classical
  rw [map_sum]
  apply Finset.sum_bij (fun e _ => reversePrefix e)
  · intro e he
    exact reversePrefix_mem he
  · intro e he f hf hef
    have het := ((mem_firstArrivals D v e).mp he).2.2
    have hft := ((mem_firstArrivals D v f).mp hf).2.2
    have h := congrArg (reverseRay v) hef
    simpa [reverseRay_reversePrefix _ _ het,reverseRay_reversePrefix _ _ hft] using h
  · intro e he
    exact ⟨reverseRay v e,reverseRay_mem hv he,reversePrefix_reverseRay _ _⟩
  · intro e he
    simp [reversePrefix]

theorem IsExcursion.distinct_ports {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : reverseGerm (terminalGerm e.1 e.2) ≠ e.1 := by
  intro hp
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil he.nonempty
  have hN := (stopped_traced D e.1 e.2 he.2.2.1).1
  rw [hw,traced,List.nodup_cons] at hN
  cases w with
  | nil =>
      have hk := congrArg Prod.snd hp
      simp only [hw,terminalGerm,reverseGerm,advance] at hk
      rcases e.1 with ⟨v,k⟩
      fin_cases k <;> cases b <;> simp [outgoingSlot] at hk
  | cons c w =>
      apply hN.1
      have hm := reverse_first_mem (advance e.1 b) (c :: w) (by simp)
      have hx : (reverseGerm (terminalGerm (advance e.1 b) (c :: w))).1 = e.1.1 :=
        congrArg Prod.fst (by simpa only [hw,terminalGerm] using hp)
      exact hx ▸ hm

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

abbrev FaceIndex := ℤ × ℤ

noncomputable def facePrefix (f : FaceIndex →₀ ℤ) (i j : ℤ) : ℤ :=
  ∑ a ∈ f.support, if a.2 = j ∧ a.1 ≤ i then f a else 0

theorem facePrefix_difference (f : FaceIndex →₀ ℤ) (i j : ℤ) :
    facePrefix f i j - facePrefix f (i - 1) j = f (i,j) := by
  classical
  unfold facePrefix
  rw [← Finset.sum_sub_distrib]
  have ht (a : FaceIndex) :
      (if a.2 = j ∧ a.1 ≤ i then f a else 0) -
        (if a.2 = j ∧ a.1 ≤ i - 1 then f a else 0) =
        if a = (i,j) then f a else 0 := by
    rcases a with ⟨x,y⟩
    by_cases hy : y = j
    · subst y
      by_cases hx : x = i
      · subst x
        simp
      · have hh : x ≤ i ↔ x ≤ i - 1 := by omega
        simp [hx,hh]
    · simp [hy]
  simp_rw [ht]
  by_cases hm : (i,j) ∈ f.support
  · simp [hm]
  · have hz : f (i,j) = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hm
    simp [hm, hz]

def InFaceBox (M : ℕ) (a : FaceIndex) : Prop :=
  -(M : ℤ) ≤ a.1 ∧ a.1 ≤ M ∧ -(M : ℤ) ≤ a.2 ∧ a.2 ≤ M

noncomputable def faceRadius (f : FaceIndex →₀ ℤ) : ℕ :=
  f.support.sup fun a => a.1.natAbs + a.2.natAbs

theorem mem_support_in_box (f : FaceIndex →₀ ℤ) (a : FaceIndex)
    (ha : a ∈ f.support) : InFaceBox (faceRadius f) a := by
  have h : a.1.natAbs + a.2.natAbs ≤ faceRadius f := Finset.le_sup (f := fun a : FaceIndex => a.1.natAbs + a.2.natAbs) ha
  have hx : a.1.natAbs ≤ faceRadius f := le_trans (Nat.le_add_right _ _) h
  have hy : a.2.natAbs ≤ faceRadius f := le_trans (Nat.le_add_left _ _) h
  have hxi : |a.1| ≤ (faceRadius f : ℤ) := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hx)
  have hyi : |a.2| ≤ (faceRadius f : ℤ) := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hy)
  exact ⟨(abs_le.mp hxi).1,(abs_le.mp hxi).2,(abs_le.mp hyi).1,(abs_le.mp hyi).2⟩

theorem facePrefix_left_zero (f : FaceIndex →₀ ℤ) (i j : ℤ)
    (hi : i < -(faceRadius f : ℤ)) : facePrefix f i j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  have hb := (mem_support_in_box f a ha).1
  have hx : ¬a.1 ≤ i := by omega
  simp [hx]

theorem facePrefix_row_zero (f : FaceIndex →₀ ℤ) (i j : ℤ)
    (hj : j < -(faceRadius f : ℤ) ∨ (faceRadius f : ℤ) < j) :
    facePrefix f i j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  have hb := mem_support_in_box f a ha
  have hy : a.2 ≠ j := by intro h; rcases hb with ⟨h1,h2,h3,h4⟩; omega
  simp [hy]

theorem int_function_constant {f : ℤ → ℤ} (hf : ∀ i, f (i + 1) = f i)
    (i j : ℤ) : f i = f j := by
  have hzero (n : ℤ) : f n = f 0 := by
    induction n using Int.induction_on with
    | zero => rfl
    | succ n hn => exact (hf n).trans hn
    | pred n hn =>
      calc f (-(n : ℤ) - 1) = f (-n) := by simpa using (hf (-(n : ℤ) - 1)).symm
           _ = f 0 := hn
  exact (hzero i).trans (hzero j).symm

structure FiniteHoneycombFlow where
  q0 : FaceIndex →₀ ℤ
  q1 : FaceIndex →₀ ℤ
  q2 : FaceIndex →₀ ℤ
  up_conservation : ∀ i j, q0 (i,j) + q1 (i,j) + q2 (i,j) = 0
  down_conservation : ∀ i j, q0 (i,j+1) + q1 (i,j) + q2 (i+1,j) = 0

noncomputable def flowPotential (q : FiniteHoneycombFlow) (i j : ℤ) : ℤ :=
  facePrefix q.q0 i j

theorem flow_difference (q : FiniteHoneycombFlow) (i j : ℤ) :
    q.q0 (i,j+1) - q.q0 (i,j) = q.q2 (i,j) - q.q2 (i+1,j) := by
  have hu := q.up_conservation i j
  have hd := q.down_conservation i j
  omega

theorem flowPotential_vertical (q : FiniteHoneycombFlow) (i j : ℤ) :
    flowPotential q i (j+1) - flowPotential q i j = -q.q2 (i+1,j) := by
  let H : ℤ → ℤ := fun k =>
    flowPotential q k (j+1) - flowPotential q k j + q.q2 (k+1,j)
  have hH : ∀ k, H (k+1) = H k := by
    intro k
    have h1 := facePrefix_difference q.q0 (k+1) (j+1)
    have h2 := facePrefix_difference q.q0 (k+1) j
    have hd := flow_difference q (k+1) j
    simp only [add_sub_cancel_right] at h1 h2
    dsimp [H,flowPotential]
    omega
  let k : ℤ := -(faceRadius q.q0 : ℤ) - (faceRadius q.q2 : ℤ) - 2
  have hk0 : k < -(faceRadius q.q0 : ℤ) := by dsimp [k]; omega
  have hk2 : q.q2 (k+1,j) = 0 := by
    by_contra hne
    have hm := Finsupp.mem_support_iff.mpr hne
    have hb := (mem_support_in_box q.q2 (k+1,j) hm).1
    dsimp [k] at hb
    omega
  have hHz : H k = 0 := by
    dsimp [H,flowPotential]
    rw [facePrefix_left_zero _ _ _ hk0,facePrefix_left_zero _ _ _ hk0,hk2]
    norm_num
  have h := (int_function_constant hH i k).trans hHz
  dsimp [H] at h
  omega

theorem flowPotential_right_zero (q : FiniteHoneycombFlow) (i j : ℤ)
    (hi : (faceRadius q.q2 : ℤ) ≤ i) : flowPotential q i j = 0 := by
  have hconstant : ∀ k, flowPotential q i (k+1) = flowPotential q i k := by
    intro k
    have hq : q.q2 (i+1,k) = 0 := by
      by_contra hne
      have hb := (mem_support_in_box q.q2 (i+1,k)
        (Finsupp.mem_support_iff.mpr hne)).2.1
      omega
    have h := flowPotential_vertical q i k
    rw [hq] at h
    omega
  let k : ℤ := (faceRadius q.q0 : ℤ) + 1
  have hz : flowPotential q i k = 0 :=
    facePrefix_row_zero q.q0 i k (Or.inr (by dsimp [k]; omega))
  exact (int_function_constant hconstant j k).trans hz

theorem flowPotential_finite_support (q : FiniteHoneycombFlow) :
    Set.Finite {a : FaceIndex | flowPotential q a.1 a.2 ≠ 0} := by
  let M : ℤ := (faceRadius q.q0 : ℤ) + faceRadius q.q2 + 1
  apply (Set.finite_Icc (-M, -M) (M, M)).subset
  intro a ha
  change flowPotential q a.1 a.2 ≠ 0 at ha
  have hleft : -(faceRadius q.q0 : ℤ) ≤ a.1 := by
    by_contra h
    exact ha (facePrefix_left_zero q.q0 a.1 a.2 (by omega))
  have hright : a.1 < (faceRadius q.q2 : ℤ) := by
    by_contra h
    exact ha (flowPotential_right_zero q a.1 a.2 (by omega))
  have hbottom : -(faceRadius q.q0 : ℤ) ≤ a.2 := by
    by_contra h
    exact ha (facePrefix_row_zero q.q0 a.1 a.2 (Or.inl (by omega)))
  have htop : a.2 ≤ (faceRadius q.q0 : ℤ) := by
    by_contra h
    exact ha (facePrefix_row_zero q.q0 a.1 a.2 (Or.inr (by omega)))
  change (-M ≤ a.1 ∧ -M ≤ a.2) ∧ a.1 ≤ M ∧ a.2 ≤ M
  dsimp [M]
  omega

noncomputable def finiteFlowPotential (q : FiniteHoneycombFlow) : FaceIndex →₀ ℤ :=
  Finsupp.ofSupportFinite (fun a => flowPotential q a.1 a.2)
    (flowPotential_finite_support q)

theorem finite_flow_is_face_boundary (q : FiniteHoneycombFlow) :
    ∃ p : FaceIndex →₀ ℤ, ∀ i j,
      q.q0 (i,j) = p (i,j) - p (i-1,j) ∧
      q.q1 (i,j) = p (i-1,j+1) - p (i,j) ∧
      q.q2 (i,j) = p (i-1,j) - p (i-1,j+1) := by
  refine ⟨finiteFlowPotential q, ?_⟩
  intro i j
  have h0 := facePrefix_difference q.q0 i j
  have h2 := flowPotential_vertical q (i-1) j
  have hu := q.up_conservation i j
  simp only [sub_add_cancel] at h2
  simp only [finiteFlowPotential,Finsupp.ofSupportFinite_coe,flowPotential]
  dsimp [flowPotential] at h2
  omega

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor
abbrev EdgeIndex := FaceIndex × Fin 3

def upEnd (e : EdgeIndex) : Vertex := .up e.1.1 e.1.2

def downEnd (e : EdgeIndex) : Vertex := neighbor (upEnd e) e.2

noncomputable def edgeBoundary : (EdgeIndex →₀ ℤ) →+ (Vertex →₀ ℤ) :=
  Finsupp.liftAddHom fun e => Finsupp.singleAddHom (upEnd e) - Finsupp.singleAddHom (downEnd e)

@[simp] theorem edgeBoundary_single (e : EdgeIndex) (a : ℤ) :
    edgeBoundary (Finsupp.single e a) =
      Finsupp.single (upEnd e) a - Finsupp.single (downEnd e) a := by
  simp [edgeBoundary]

def edgeOf : Germ → EdgeIndex
  | (.up i j, k) => ((i,j),k)
  | (.down i j, k) =>
      if k = 0 then ((i,j+1),k) else if k = 1 then ((i,j),k) else ((i+1,j),k)

def dartSign : Germ → ℤ
  | (.up _ _, _) => 1
  | (.down _ _, _) => -1

noncomputable def dartFlow (g : Germ) : EdgeIndex →₀ ℤ :=
  Finsupp.single (edgeOf g) (dartSign g)

@[simp] theorem edgeBoundary_dartFlow (g : Germ) :
    edgeBoundary (dartFlow g) =
      Finsupp.single g.1 1 - Finsupp.single (neighbor g.1 g.2) 1 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [dartFlow,edgeOf,dartSign,upEnd,downEnd,neighbor]

noncomputable def wordFlow : Germ → List Bool → (EdgeIndex →₀ ℤ)
  | _, [] => 0
  | g, b :: w => dartFlow (g.1,outgoingSlot g b) + wordFlow (advance g b) w

theorem boundary_wordFlow (g : Germ) (w : List Bool) :
    edgeBoundary (wordFlow g w) =
      Finsupp.single g.1 1 - Finsupp.single (terminalGerm g w).1 1 := by
  induction w generalizing g with
  | nil => simp [wordFlow,terminalGerm]
  | cons b w ih =>
      simp only [wordFlow,map_add,edgeBoundary_dartFlow,ih,terminalGerm]
      simp only [advance]
      abel

noncomputable def flowComponent (q : EdgeIndex →₀ ℤ) (k : Fin 3) : FaceIndex →₀ ℤ :=
  Finsupp.comapDomain (fun a => (a,k)) q (by intro a _ b _ h; exact Prod.mk.inj h |>.1)

@[simp] theorem flowComponent_apply (q : EdgeIndex →₀ ℤ) (k : Fin 3) (a : FaceIndex) :
    flowComponent q k a = q (a,k) := rfl

theorem boundary_up (q : EdgeIndex →₀ ℤ) (i j : ℤ) :
    edgeBoundary q (.up i j) = q ((i,j),0) + q ((i,j),1) + q ((i,j),2) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      fin_cases k <;>
        simp [edgeBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem boundary_down (q : EdgeIndex →₀ ℤ) (i j : ℤ) :
    edgeBoundary q (.down i j) =
      -(q ((i,j+1),0) + q ((i,j),1) + q ((i+1,j),2)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      have hy : j = y - 1 ↔ y = j + 1 := by omega
      have hx : i = x - 1 ↔ x = i + 1 := by omega
      fin_cases k <;>
        simp [edgeBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

noncomputable def closedWordFlow (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) : FiniteHoneycombFlow where
  q0 := flowComponent (wordFlow g w) 0
  q1 := flowComponent (wordFlow g w) 1
  q2 := flowComponent (wordFlow g w) 2
  up_conservation := by
    intro i j
    simp only [flowComponent_apply]
    rw [← boundary_up,boundary_wordFlow,hc,sub_self]
    rfl
  down_conservation := by
    intro i j
    simp only [flowComponent_apply]
    have h := boundary_down (wordFlow g w) i j
    rw [boundary_wordFlow,hc,sub_self] at h
    simp only [Finsupp.zero_apply] at h
    omega

theorem closed_word_has_finite_potential (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) :
    ∃ p : FaceIndex →₀ ℤ, ∀ i j,
      wordFlow g w ((i,j),0) = p (i,j) - p (i-1,j) ∧
      wordFlow g w ((i,j),1) = p (i-1,j+1) - p (i,j) ∧
      wordFlow g w ((i,j),2) = p (i-1,j) - p (i-1,j+1) := by
  exact finite_flow_is_face_boundary (closedWordFlow g w hc)

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def orientedFlow : (EdgeIndex →₀ ℤ) →+ (Germ →₀ ℤ) :=
  Finsupp.liftAddHom fun e =>
    Finsupp.singleAddHom (upEnd e,e.2) - Finsupp.singleAddHom (downEnd e,e.2)

@[simp] theorem orientedFlow_single (e : EdgeIndex) (a : ℤ) :
    orientedFlow (Finsupp.single e a) =
      Finsupp.single (upEnd e,e.2) a - Finsupp.single (downEnd e,e.2) a := by
  simp [orientedFlow]

@[simp] theorem orientedFlow_dartFlow (g : Germ) :
    orientedFlow (dartFlow g) = Finsupp.single g 1 - Finsupp.single (reverseGerm g) 1 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [dartFlow,edgeOf,dartSign,upEnd,downEnd,neighbor,reverseGerm]

noncomputable def turnVisit : Germ → List Bool → (Germ →₀ ℤ)
  | _, [] => 0
  | g, b :: w =>
      Finsupp.single (g.1,outgoingSlot g b) 1 - Finsupp.single g 1 +
        turnVisit (advance g b) w

theorem orientedFlow_wordFlow (g : Germ) (w : List Bool) :
    orientedFlow (wordFlow g w) =
      turnVisit g w + Finsupp.single g 1 - Finsupp.single (terminalGerm g w) 1 := by
  induction w generalizing g with
  | nil => simp [wordFlow,turnVisit,terminalGerm]
  | cons b w ih =>
      simp only [wordFlow,map_add,orientedFlow_dartFlow,turnVisit,terminalGerm,ih]
      have h : reverseGerm (g.1,outgoingSlot g b) = advance g b := rfl
      rw [h]
      abel

theorem turnVisit_eq_zero_of_not_mem (g : Germ) (w : List Bool) (v : Vertex)
    (k : Fin 3) (hv : v ∉ traced g w) : turnVisit g w (v,k) = 0 := by
  classical
  induction w generalizing g with
  | nil => simp [turnVisit]
  | cons b w ih =>
      simp only [traced,List.mem_cons,not_or] at hv
      have hne : (v,k) ≠ g := by intro h; exact hv.1 (congrArg Prod.fst h)
      have hne' : (g.1,outgoingSlot g b) ≠ (v,k) := by
        intro h; exact hv.1 (congrArg Prod.fst h).symm
      simp [turnVisit,ih _ hv.2,hne,hne']

theorem simple_closed_word_local (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup) (hc : terminalGerm g (b :: w) = g)
    (k : Fin 3) :
    orientedFlow (wordFlow g (b :: w)) (g.1,k) =
      (if k = outgoingSlot g b then 1 else 0) - (if k = g.2 then 1 else 0) := by
  classical
  rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
  simp only [traced,List.nodup_cons] at hN
  have ht := turnVisit_eq_zero_of_not_mem (advance g b) w g.1 k hN.1
  rcases g with ⟨v,j⟩
  simp [turnVisit,ht,Finsupp.single_apply,eq_comm]

theorem orientedFlow_up (q : EdgeIndex →₀ ℤ) (i j : ℤ) (k : Fin 3) :
    orientedFlow q (.up i j,k) = q ((i,j),k) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]
  | single e a =>
      rcases e with ⟨⟨x,y⟩,l⟩
      fin_cases l <;> fin_cases k <;>
        simp [orientedFlow_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem orientedFlow_down (q : EdgeIndex →₀ ℤ) (i j : ℤ) (k : Fin 3) :
    orientedFlow q (.down i j,k) = -q (edgeOf (.down i j,k)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,l⟩
      have hy : j = y - 1 ↔ y = j + 1 := by omega
      have hx : i = x - 1 ↔ x = i + 1 := by omega
      fin_cases l <;> fin_cases k <;>
        simp [orientedFlow_single,edgeOf,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

def leftFace : Germ → FaceIndex
  | (.up i j,k) => if k = 0 then (i,j) else if k = 1 then (i-1,j+1) else (i-1,j)
  | (.down i j,k) => if k = 0 then (i-1,j+1) else if k = 1 then (i,j) else (i,j+1)

def rightFace (g : Germ) : FaceIndex := leftFace (reverseGerm g)

def RepresentsFlow (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ) : Prop :=
  ∀ g : Germ, orientedFlow q g = p (leftFace g) - p (rightFace g)

theorem closed_word_has_potential (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) :
    ∃ p : FaceIndex →₀ ℤ, RepresentsFlow p (wordFlow g w) := by
  obtain ⟨p,hp⟩ := closed_word_has_finite_potential g w hc
  refine ⟨p, ?_⟩
  intro d
  rcases d with ⟨v,k⟩
  cases v with
  | up i j =>
      have h := hp i j
      fin_cases k <;>
        simp [orientedFlow_up,leftFace,rightFace,reverseGerm,neighbor] <;> omega
  | down i j =>
      have h0 := (hp i (j+1)).1
      have h1 := (hp i j).2.1
      have h2 := (hp (i+1) j).2.2
      fin_cases k <;>
        simp [orientedFlow_down,edgeOf,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega



@[simp] theorem wordFlow_append (g : Germ) (u w : List Bool) :
    wordFlow g (u ++ w) = wordFlow g u + wordFlow (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => simp [wordFlow,terminalGerm]
  | cons b u ih => simp [wordFlow,terminalGerm,ih,add_assoc]

theorem closed_word_rotate (g : Germ) (u w : List Bool)
    (hN : (traced g (u ++ w)).Nodup) (hc : terminalGerm g (u ++ w) = g) :
    let g' := terminalGerm g u
    (traced g' (w ++ u)).Nodup ∧
    terminalGerm g' (w ++ u) = g' ∧ wordFlow g' (w ++ u) = wordFlow g (u ++ w) := by
  dsimp only
  have ht : terminalGerm (terminalGerm g u) w = g := by simpa using hc
  rw [traced_append] at hN
  simp only [traced_append,terminalGerm_append,wordFlow_append,ht]
  exact ⟨List.nodup_append_comm.mp hN,trivial,add_comm _ _⟩

def LocalContour (q : EdgeIndex →₀ ℤ) (g : Germ) (b : Bool) : Prop :=
  ∀ k : Fin 3, orientedFlow q (g.1,k) =
    (if k = outgoingSlot g b then 1 else 0) - (if k = g.2 then 1 else 0)

def WordContour (q : EdgeIndex →₀ ℤ) : Germ → List Bool → Prop
  | _, [] => True
  | g, b :: w => LocalContour q g b ∧ WordContour q (advance g b) w

theorem wordContour_of_splits (q : EdgeIndex →₀ ℤ) (g : Germ) (w : List Bool)
    (hs : ∀ u b v, w = u ++ b :: v → LocalContour q (terminalGerm g u) b) :
    WordContour q g w := by
  induction w generalizing g with
  | nil => trivial
  | cons b w ih =>
      refine ⟨by simpa only [terminalGerm] using hs [] b w rfl, ih (advance g b) ?_⟩
      intro u c v hv
      simpa only [terminalGerm] using hs (b :: u) c v (by simp [hv])

theorem simple_closed_word_contour (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    WordContour (wordFlow g w) g w := by
  apply wordContour_of_splits
  intro u b v h
  subst w
  obtain ⟨hN',hc',hq⟩ := closed_word_rotate g u (b :: v) hN hc
  rw [← hq]
  intro k
  exact simple_closed_word_local (terminalGerm g u) b (v ++ u) hN' hc' k

theorem localContour_sides (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (b : Bool) (hl : LocalContour q g b) :
    p (rightFace (advance g b)) = p (rightFace g) ∧
    p (leftFace (advance g b)) = p (leftFace g) ∧
    p (rightFace g) - p (leftFace g) = 1 := by
  have h0 := (hp (g.1,0)).symm.trans (hl 0)
  have h1 := (hp (g.1,1)).symm.trans (hl 1)
  have h2 := (hp (g.1,2)).symm.trans (hl 2)
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    simp [advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

theorem wordContour_sides (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (w : List Bool) (hw : WordContour q g w) :
    p (rightFace (terminalGerm g w)) = p (rightFace g) ∧
      p (leftFace (terminalGerm g w)) = p (leftFace g) := by
  induction w generalizing g with
  | nil => exact ⟨rfl,rfl⟩
  | cons b w ih =>
      obtain ⟨hr,hl,_⟩ := localContour_sides p q hp g b hw.1
      obtain ⟨hr',hl'⟩ := ih (advance g b) hw.2
      exact ⟨hr'.trans hr,hl'.trans hl⟩



@[simp] theorem rightFace_reverse (g : Germ) :
    rightFace (reverseGerm g) = leftFace g := by simp [rightFace]

@[simp] theorem reverseGerm_advance (g : Germ) (b : Bool) :
    reverseGerm (advance g b) = (g.1,outgoingSlot g b) := by
  simp [reverseGerm,advance]

def canonicalDart (e : EdgeIndex) : Germ := (upEnd e,e.2)

theorem canonicalDart_edgeOf (g : Germ) :
    canonicalDart (edgeOf g) = g ∨ canonicalDart (edgeOf g) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [canonicalDart,edgeOf,upEnd,reverseGerm,neighbor]

def SideValues (p : FaceIndex →₀ ℤ) (L R : ℤ) (g : Germ) : Prop :=
  (p (leftFace g) = L ∨ p (leftFace g) = R) ∧
    (p (rightFace g) = L ∨ p (rightFace g) = R)

theorem SideValues.reverse {p : FaceIndex →₀ ℤ} {L R : ℤ} {g : Germ}
    (h : SideValues p L R g) : SideValues p L R (reverseGerm g) := by
  exact ⟨h.2,by simpa only [rightFace_reverse] using h.1⟩

theorem SideValues.canonical {p : FaceIndex →₀ ℤ} {L R : ℤ} {g : Germ}
    (h : SideValues p L R g) : SideValues p L R (canonicalDart (edgeOf g)) := by
  rcases canonicalDart_edgeOf g with he | he
  · exact he ▸ h
  · exact he ▸ h.reverse

theorem wordFlow_edge_sides (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (w : List Bool) (hw : WordContour q g w)
    (e : EdgeIndex) (he : wordFlow g w e ≠ 0) :
    SideValues p (p (rightFace g)) (p (leftFace g)) (canonicalDart e) := by
  classical
  induction w generalizing g with
  | nil => simp [wordFlow] at he
  | cons b w ih =>
      obtain ⟨hr,hl,_⟩ := localContour_sides p q hp g b hw.1
      by_cases hz : dartFlow (g.1,outgoingSlot g b) e = 0
      · have ht : wordFlow (advance g b) w e ≠ 0 := by
          simpa only [wordFlow,Finsupp.add_apply,hz,zero_add] using he
        have hs := ih (advance g b) hw.2 ht
        rw [hr,hl] at hs
        exact hs
      · have heq : edgeOf (g.1,outgoingSlot g b) = e := by
          by_contra h
          exact hz (by simp [dartFlow,h])
        have hs : SideValues p (p (rightFace g)) (p (leftFace g)) (advance g b) :=
          ⟨Or.inr hl,Or.inl hr⟩
        have hs' := hs.reverse.canonical
        simpa only [reverseGerm_advance,heq] using hs'

theorem RepresentsFlow.horizontal {p : FaceIndex →₀ ℤ} {q : EdgeIndex →₀ ℤ}
    (hp : RepresentsFlow p q) (i j : ℤ) :
    q ((i,j),0) = p (i,j) - p (i-1,j) := by
  simpa [orientedFlow_up,leftFace,rightFace,reverseGerm,neighbor] using hp (.up i j,0)



theorem finite_potential_has_zero_side (p : FaceIndex →₀ ℤ) (hp : p ≠ 0) :
    ∃ i j : ℤ, p (i,j) ≠ 0 ∧ p (i-1,j) = 0 := by
  classical
  let S : Finset ℤ := p.support.image Prod.fst
  have hS : S.Nonempty := (Finsupp.support_nonempty_iff.mpr hp).image Prod.fst
  obtain ⟨a,ha,hmin⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
  refine ⟨a.1,a.2,Finsupp.mem_support_iff.mp ha,?_⟩
  by_contra hne
  have hm : a.1 - 1 ∈ S := Finset.mem_image.mpr
    ⟨(a.1-1,a.2),Finsupp.mem_support_iff.mpr hne,rfl⟩
  have h := Finset.min'_le S (a.1-1) hm
  omega

theorem finite_potential_two_values (p : FaceIndex →₀ ℤ) (L R : ℤ) (hp : p ≠ 0)
    (hgrad : ∀ i j : ℤ, p (i,j) - p (i-1,j) ≠ 0 →
      (p (i,j) = L ∨ p (i,j) = R) ∧ (p (i-1,j) = L ∨ p (i-1,j) = R)) :
    (L = 0 ∨ R = 0) ∧ ∀ a : FaceIndex, p a = L ∨ p a = R := by
  obtain ⟨i,j,hne,hzero⟩ := finite_potential_has_zero_side p hp
  have hz : L = 0 ∨ R = 0 := by
    have h := (hgrad i j (by simpa [hzero] using hne)).2
    rw [hzero] at h
    exact h.imp Eq.symm Eq.symm
  refine ⟨hz,?_⟩
  rintro ⟨i,j⟩
  let m : ℤ := -(faceRadius p : ℤ) - 1
  have hleft (k : ℤ) (hk : k ≤ m) : p (k,j) = 0 := by
    by_contra hne
    have hb := (mem_support_in_box p (k,j) (Finsupp.mem_support_iff.mpr hne)).1
    dsimp [m] at hk
    omega
  have hbase : p (m,j) = L ∨ p (m,j) = R := by
    rw [hleft m le_rfl]
    exact hz.imp Eq.symm Eq.symm
  by_cases him : i ≤ m
  · rw [hleft i him]
    exact hz.imp Eq.symm Eq.symm
  · have hmi : m ≤ i := by omega
    apply Int.leInduction (motive := fun k _ => p (k,j) = L ∨ p (k,j) = R) hbase ?_ i hmi
    intro k _ hk
    by_cases hg : p (k+1,j) - p (k,j) = 0
    · have heq : p (k+1,j) = p (k,j) := by omega
      exact heq ▸ hk
    · simpa only [add_sub_cancel_right] using (hgrad (k+1) j (by simpa using hg)).1

theorem simple_closed_word_indicator (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    ∃ (p : FaceIndex →₀ ℤ) (ε : ℤ), RepresentsFlow p (wordFlow g w) ∧ p ≠ 0 ∧
      (ε = 1 ∨ ε = -1) ∧ ∀ a : FaceIndex, p a = 0 ∨ p a = ε := by
  obtain ⟨p,hp⟩ := closed_word_has_potential g w hc
  have hw := simple_closed_word_contour g w hN hc
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hne
  have hs := localContour_sides p (wordFlow g (b :: u)) hp g b hw.1
  let L := p (rightFace g)
  let R := p (leftFace g)
  have hLR : L - R = 1 := hs.2.2
  have hpne : p ≠ 0 := by
    intro hz
    simp only [L,R,hz,Finsupp.zero_apply,sub_zero] at hLR
    omega
  have ht : (L = 0 ∨ R = 0) ∧ ∀ a : FaceIndex, p a = L ∨ p a = R := by
    apply finite_potential_two_values p L R hpne
    intro i j hij
    have hq : wordFlow g (b :: u) ((i,j),0) ≠ 0 := by
      simpa only [hp.horizontal i j] using hij
    have h := wordFlow_edge_sides p _ hp g (b :: u) hw ((i,j),0) hq
    simpa [SideValues,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor,L,R] using h
  rcases ht.1 with hL | hR
  · have hRm : R = -1 := by omega
    refine ⟨p,-1,hp,hpne,Or.inr rfl,?_⟩
    intro a
    simpa only [hL,hRm] using ht.2 a
  · have hLp : L = 1 := by omega
    refine ⟨p,1,hp,hpne,Or.inl rfl,?_⟩
    intro a
    simpa only [hLp,hR,or_comm] using ht.2 a

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def faceEdges (a : FaceIndex) : Finset EdgeIndex :=
  {((a.1,a.2),0), ((a.1+1,a.2),0),
   ((a.1+1,a.2-1),1), ((a.1,a.2),1),
   ((a.1+1,a.2),2), ((a.1+1,a.2-1),2)}

def faceVertices (a : FaceIndex) : Finset Vertex :=
  {.up a.1 a.2, .down a.1 (a.2-1), .up (a.1+1) (a.2-1),
   .down a.1 a.2, .up (a.1+1) a.2, .down (a.1+1) (a.2-1)}

def cellEdges (S : Finset FaceIndex) : Finset EdgeIndex := S.biUnion faceEdges

def cellVertices (S : Finset FaceIndex) : Finset Vertex := S.biUnion faceVertices

theorem mem_faceEdges (e : EdgeIndex) (a : FaceIndex) :
    e ∈ faceEdges a ↔ leftFace (canonicalDart e) = a ∨ rightFace (canonicalDart e) = a := by
  rcases e with ⟨⟨i,j⟩,k⟩
  rcases a with ⟨x,y⟩
  fin_cases k <;>
    simp [faceEdges,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] <;> omega

theorem mem_faceVertices (v : Vertex) (a : FaceIndex) :
    v ∈ faceVertices a ↔ ∃ k : Fin 3, leftFace (v,k) = a := by
  rcases a with ⟨x,y⟩
  cases v <;>
    simp [faceVertices,Fin.exists_fin_succ,leftFace] <;> omega

theorem mem_cellEdges (S : Finset FaceIndex) (e : EdgeIndex) :
    e ∈ cellEdges S ↔ leftFace (canonicalDart e) ∈ S ∨ rightFace (canonicalDart e) ∈ S := by
  simp only [cellEdges,Finset.mem_biUnion,mem_faceEdges]
  constructor
  · rintro ⟨a,ha,h | h⟩
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (h ▸ ha)
  · rintro (h | h)
    · exact ⟨_,h,Or.inl rfl⟩
    · exact ⟨_,h,Or.inr rfl⟩

theorem mem_cellVertices (S : Finset FaceIndex) (v : Vertex) :
    v ∈ cellVertices S ↔ ∃ k : Fin 3, leftFace (v,k) ∈ S := by
  simp only [cellVertices,Finset.mem_biUnion,mem_faceVertices]
  constructor
  · rintro ⟨a,ha,k,hk⟩
    exact ⟨k,hk ▸ ha⟩
  · rintro ⟨k,hk⟩
    exact ⟨_,hk,k,rfl⟩

theorem edge_mem_vertex (S : Finset FaceIndex) (g : Germ)
    (h : edgeOf g ∈ cellEdges S) : g.1 ∈ cellVertices S := by
  rw [mem_cellEdges] at h
  rcases canonicalDart_edgeOf g with hg | hg
  · rw [hg] at h
    rcases h with h | h
    · exact (mem_cellVertices S g.1).mpr ⟨g.2,h⟩
    · rcases g with ⟨v,k⟩
      rw [mem_cellVertices]
      cases v <;> fin_cases k <;>
        simp [rightFace,reverseGerm,neighbor] at h <;>
        simp_all [Fin.exists_fin_succ,leftFace]
  · rw [hg,rightFace_reverse] at h
    rcases h with h | h
    · rcases g with ⟨v,k⟩
      rw [mem_cellVertices]
      cases v <;> fin_cases k <;>
        simp [reverseGerm,neighbor] at h <;>
        simp_all [Fin.exists_fin_succ,leftFace]
    · exact (mem_cellVertices S g.1).mpr ⟨g.2,h⟩

@[simp] theorem edgeOf_reverse (g : Germ) : edgeOf (reverseGerm g) = edgeOf g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [edgeOf,reverseGerm,neighbor]

theorem edge_mem_neighbor (S : Finset FaceIndex) (g : Germ)
    (h : edgeOf g ∈ cellEdges S) : neighbor g.1 g.2 ∈ cellVertices S := by
  exact edge_mem_vertex S (reverseGerm g) (by simpa using h)

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor.QFlow

abbrev FaceIndex := ℤ × ℤ

noncomputable def facePrefix (f : FaceIndex →₀ ℚ) (i j : ℤ) : ℚ :=
  ∑ a ∈ f.support, if a.2 = j ∧ a.1 ≤ i then f a else 0

theorem facePrefix_difference (f : FaceIndex →₀ ℚ) (i j : ℤ) :
    facePrefix f i j - facePrefix f (i - 1) j = f (i,j) := by
  classical
  unfold facePrefix
  rw [← Finset.sum_sub_distrib]
  have ht (a : FaceIndex) :
      (if a.2 = j ∧ a.1 ≤ i then f a else 0) -
        (if a.2 = j ∧ a.1 ≤ i - 1 then f a else 0) =
        if a = (i,j) then f a else 0 := by
    rcases a with ⟨x,y⟩
    by_cases hy : y = j
    · subst y
      by_cases hx : x = i
      · subst x
        simp
      · have hh : x ≤ i ↔ x ≤ i - 1 := by omega
        simp [hx,hh]
    · simp [hy]
  simp_rw [ht]
  by_cases hm : (i,j) ∈ f.support
  · simp [hm]
  · have hz : f (i,j) = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hm
    simp [hm, hz]

def InFaceBox (M : ℕ) (a : FaceIndex) : Prop :=
  -(M : ℤ) ≤ a.1 ∧ a.1 ≤ M ∧ -(M : ℤ) ≤ a.2 ∧ a.2 ≤ M

noncomputable def faceRadius (f : FaceIndex →₀ ℚ) : ℕ :=
  f.support.sup fun a => a.1.natAbs + a.2.natAbs

theorem mem_support_in_box (f : FaceIndex →₀ ℚ) (a : FaceIndex)
    (ha : a ∈ f.support) : InFaceBox (faceRadius f) a := by
  have h : a.1.natAbs + a.2.natAbs ≤ faceRadius f := Finset.le_sup (f := fun a : FaceIndex => a.1.natAbs + a.2.natAbs) ha
  have hx : a.1.natAbs ≤ faceRadius f := le_trans (Nat.le_add_right _ _) h
  have hy : a.2.natAbs ≤ faceRadius f := le_trans (Nat.le_add_left _ _) h
  have hxi : |a.1| ≤ (faceRadius f : ℤ) := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hx)
  have hyi : |a.2| ≤ (faceRadius f : ℤ) := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hy)
  exact ⟨(abs_le.mp hxi).1,(abs_le.mp hxi).2,(abs_le.mp hyi).1,(abs_le.mp hyi).2⟩

theorem facePrefix_left_zero (f : FaceIndex →₀ ℚ) (i j : ℤ)
    (hi : i < -(faceRadius f : ℤ)) : facePrefix f i j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  have hb := (mem_support_in_box f a ha).1
  have hx : ¬a.1 ≤ i := by omega
  simp [hx]

theorem facePrefix_row_zero (f : FaceIndex →₀ ℚ) (i j : ℤ)
    (hj : j < -(faceRadius f : ℤ) ∨ (faceRadius f : ℤ) < j) :
    facePrefix f i j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  have hb := mem_support_in_box f a ha
  have hy : a.2 ≠ j := by intro h; rcases hb with ⟨h1,h2,h3,h4⟩; omega
  simp [hy]

theorem int_function_constant {f : ℤ → ℚ} (hf : ∀ i, f (i + 1) = f i)
    (i j : ℤ) : f i = f j := by
  have hzero (n : ℤ) : f n = f 0 := by
    induction n using Int.induction_on with
    | zero => rfl
    | succ n hn => exact (hf n).trans hn
    | pred n hn =>
      calc f (-(n : ℤ) - 1) = f (-n) := by simpa using (hf (-(n : ℤ) - 1)).symm
           _ = f 0 := hn
  exact (hzero i).trans (hzero j).symm

structure FiniteHoneycombFlow where
  q0 : FaceIndex →₀ ℚ
  q1 : FaceIndex →₀ ℚ
  q2 : FaceIndex →₀ ℚ
  up_conservation : ∀ i j, q0 (i,j) + q1 (i,j) + q2 (i,j) = 0
  down_conservation : ∀ i j, q0 (i,j+1) + q1 (i,j) + q2 (i+1,j) = 0

noncomputable def flowPotential (q : FiniteHoneycombFlow) (i j : ℤ) : ℚ :=
  facePrefix q.q0 i j

theorem flow_difference (q : FiniteHoneycombFlow) (i j : ℤ) :
    q.q0 (i,j+1) - q.q0 (i,j) = q.q2 (i,j) - q.q2 (i+1,j) := by
  have hu := q.up_conservation i j
  have hd := q.down_conservation i j
  linarith

theorem flowPotential_vertical (q : FiniteHoneycombFlow) (i j : ℤ) :
    flowPotential q i (j+1) - flowPotential q i j = -q.q2 (i+1,j) := by
  let H : ℤ → ℚ := fun k =>
    flowPotential q k (j+1) - flowPotential q k j + q.q2 (k+1,j)
  have hH : ∀ k, H (k+1) = H k := by
    intro k
    have h1 := facePrefix_difference q.q0 (k+1) (j+1)
    have h2 := facePrefix_difference q.q0 (k+1) j
    have hd := flow_difference q (k+1) j
    simp only [add_sub_cancel_right] at h1 h2
    dsimp [H,flowPotential]
    linarith
  let k : ℤ := -(faceRadius q.q0 : ℤ) - (faceRadius q.q2 : ℤ) - 2
  have hk0 : k < -(faceRadius q.q0 : ℤ) := by dsimp [k]; omega
  have hk2 : q.q2 (k+1,j) = 0 := by
    by_contra hne
    have hm := Finsupp.mem_support_iff.mpr hne
    have hb := (mem_support_in_box q.q2 (k+1,j) hm).1
    dsimp [k] at hb
    omega
  have hHz : H k = 0 := by
    dsimp [H,flowPotential]
    rw [facePrefix_left_zero _ _ _ hk0,facePrefix_left_zero _ _ _ hk0,hk2]
    norm_num
  have h := (int_function_constant hH i k).trans hHz
  dsimp [H] at h
  linarith

theorem flowPotential_right_zero (q : FiniteHoneycombFlow) (i j : ℤ)
    (hi : (faceRadius q.q2 : ℤ) ≤ i) : flowPotential q i j = 0 := by
  have hconstant : ∀ k, flowPotential q i (k+1) = flowPotential q i k := by
    intro k
    have hq : q.q2 (i+1,k) = 0 := by
      by_contra hne
      have hb := (mem_support_in_box q.q2 (i+1,k)
        (Finsupp.mem_support_iff.mpr hne)).2.1
      omega
    have h := flowPotential_vertical q i k
    rw [hq] at h
    linarith
  let k : ℤ := (faceRadius q.q0 : ℤ) + 1
  have hz : flowPotential q i k = 0 :=
    facePrefix_row_zero q.q0 i k (Or.inr (by dsimp [k]; omega))
  exact (int_function_constant hconstant j k).trans hz

theorem flowPotential_finite_support (q : FiniteHoneycombFlow) :
    Set.Finite {a : FaceIndex | flowPotential q a.1 a.2 ≠ 0} := by
  let M : ℤ := (faceRadius q.q0 : ℤ) + faceRadius q.q2 + 1
  apply (Set.finite_Icc (-M, -M) (M, M)).subset
  intro a ha
  change flowPotential q a.1 a.2 ≠ 0 at ha
  have hleft : -(faceRadius q.q0 : ℤ) ≤ a.1 := by
    by_contra h
    exact ha (facePrefix_left_zero q.q0 a.1 a.2 (by omega))
  have hright : a.1 < (faceRadius q.q2 : ℤ) := by
    by_contra h
    exact ha (flowPotential_right_zero q a.1 a.2 (by omega))
  have hbottom : -(faceRadius q.q0 : ℤ) ≤ a.2 := by
    by_contra h
    exact ha (facePrefix_row_zero q.q0 a.1 a.2 (Or.inl (by omega)))
  have htop : a.2 ≤ (faceRadius q.q0 : ℤ) := by
    by_contra h
    exact ha (facePrefix_row_zero q.q0 a.1 a.2 (Or.inr (by omega)))
  change (-M ≤ a.1 ∧ -M ≤ a.2) ∧ a.1 ≤ M ∧ a.2 ≤ M
  dsimp [M]
  omega

noncomputable def finiteFlowPotential (q : FiniteHoneycombFlow) : FaceIndex →₀ ℚ :=
  Finsupp.ofSupportFinite (fun a => flowPotential q a.1 a.2)
    (flowPotential_finite_support q)

theorem finite_flow_is_face_boundary (q : FiniteHoneycombFlow) :
    ∃ p : FaceIndex →₀ ℚ, ∀ i j,
      q.q0 (i,j) = p (i,j) - p (i-1,j) ∧
      q.q1 (i,j) = p (i-1,j+1) - p (i,j) ∧
      q.q2 (i,j) = p (i-1,j) - p (i-1,j+1) := by
  refine ⟨finiteFlowPotential q, ?_⟩
  intro i j
  have h0 := facePrefix_difference q.q0 i j
  have h2 := flowPotential_vertical q (i-1) j
  have hu := q.up_conservation i j
  simp only [sub_add_cancel] at h2
  simp only [finiteFlowPotential,Finsupp.ofSupportFinite_coe,flowPotential]
  dsimp [flowPotential] at h2
  constructor
  · linarith
  constructor <;> linarith

end PolynomialVacuumBridge.Corridor.QFlow

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def directedCurrent (q : EdgeIndex → ℚ) (g : Germ) : ℚ :=
  (dartSign g : ℚ) * q (edgeOf g)

def ConservedCurrent (q : EdgeIndex → ℚ) : Prop :=
  ∀ v : Vertex, ∑ k : Fin 3, directedCurrent q (v,k) = 0

@[simp] theorem directedCurrent_reverse (q : EdgeIndex → ℚ) (g : Germ) :
    directedCurrent q (reverseGerm g) = -directedCurrent q g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [directedCurrent,dartSign,edgeOf,reverseGerm,neighbor]

@[simp] theorem directedCurrent_advance (q : EdgeIndex → ℚ) (g : Germ) (b : Bool) :
    directedCurrent q (advance g b) = -directedCurrent q (g.1,outgoingSlot g b) := by
  have h := directedCurrent_reverse q (advance g b)
  rw [reverseGerm_advance] at h
  linarith

theorem orientedFlow_zero_iff (q : EdgeIndex →₀ ℤ) (g : Germ) :
    orientedFlow q g = 0 ↔ q (edgeOf g) = 0 := by
  rcases g with ⟨v,k⟩
  cases v <;> simp [orientedFlow_up,orientedFlow_down,edgeOf]

theorem directedCurrent_cast (q : EdgeIndex →₀ ℤ) (g : Germ) :
    directedCurrent (fun e => (q e : ℚ)) g = (orientedFlow q g : ℚ) := by
  rcases g with ⟨v,k⟩
  cases v <;> simp [directedCurrent,dartSign,orientedFlow_up,orientedFlow_down,edgeOf]

theorem local_contour_current (p : EdgeIndex →₀ ℤ) (q : EdgeIndex → ℚ)
    (hq : ConservedCurrent q) (hs : ∀ e, p e = 0 → q e = 0)
    (g : Germ) (b : Bool) (hl : LocalContour p g b) :
    directedCurrent q (advance g b) = directedCurrent q g ∧
      ∀ k : Fin 3, directedCurrent q (g.1,k) =
        -directedCurrent q g * (orientedFlow p (g.1,k) : ℚ) := by
  have hz (k : Fin 3) :
      (if k = outgoingSlot g b then (1 : ℤ) else 0) -
        (if k = g.2 then 1 else 0) = 0 → directedCurrent q (g.1,k) = 0 := by
    intro h
    have h0 : orientedFlow p (g.1,k) = 0 := (hl k).trans h
    have he := hs (edgeOf (g.1,k)) ((orientedFlow_zero_iff p _).mp h0)
    simp [directedCurrent,he]
  have hsum := hq g.1
  rw [directedCurrent_advance]
  constructor
  · rcases g with ⟨v,k⟩
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    fin_cases k <;> cases b <;>
      simp [outgoingSlot,Fin.sum_univ_succ] at hz0 hz1 hz2 hsum ⊢ <;> linarith
  · intro k
    rw [hl k]
    rcases g with ⟨v,l⟩
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    fin_cases l <;> cases b <;> fin_cases k <;>
      simp [outgoingSlot,Fin.sum_univ_succ] at hz0 hz1 hz2 hsum ⊢ <;> linarith

theorem word_contour_current (p : EdgeIndex →₀ ℤ) (q : EdgeIndex → ℚ)
    (hq : ConservedCurrent q) (hs : ∀ e, p e = 0 → q e = 0)
    (g : Germ) (w : List Bool) (hw : WordContour p g w) :
    directedCurrent q (terminalGerm g w) = directedCurrent q g ∧
    ∀ e : EdgeIndex, wordFlow g w e ≠ 0 →
      q e = -directedCurrent q g * (p e : ℚ) := by
  induction w generalizing g with
  | nil => simp [terminalGerm,wordFlow]
  | cons b w ih =>
      obtain ⟨hstep,hlocal⟩ := local_contour_current p q hq hs g b hw.1
      obtain ⟨hend,hedge⟩ := ih (advance g b) hw.2
      constructor
      · exact hend.trans hstep
      · intro e he
        by_cases ht : wordFlow (advance g b) w e ≠ 0
        · simpa only [hstep] using hedge e ht
        · have hd : dartFlow (g.1,outgoingSlot g b) e ≠ 0 := by
            simpa only [wordFlow,Finsupp.add_apply,not_not.mp ht,add_zero] using he
          have heq : e = edgeOf (g.1,outgoingSlot g b) := by
            by_contra h
            exact hd (by simp [dartFlow,h])
          subst e
          have h := hlocal (outgoingSlot g b)
          rcases g with ⟨v,k⟩
          cases v <;>
            simp [directedCurrent,dartSign,edgeOf,orientedFlow_up,orientedFlow_down] at h ⊢ <;>
            linarith

theorem simple_cycle_current_scalar (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (q : EdgeIndex → ℚ) (hq : ConservedCurrent q)
    (hs : ∀ e, wordFlow g w e = 0 → q e = 0) :
    ∃ c : ℚ, ∀ e, q e = c * (wordFlow g w e : ℚ) := by
  refine ⟨-directedCurrent q g,?_⟩
  intro e
  by_cases he : wordFlow g w e = 0
  · simp [hs e he,he]
  · exact (word_contour_current _ q hq hs g w
      (simple_closed_word_contour g w hN hc)).2 e he

def faceGradient (r : FaceIndex → ℚ) (e : EdgeIndex) : ℚ :=
  r (leftFace (canonicalDart e)) - r (rightFace (canonicalDart e))

theorem directedCurrent_gradient (r : FaceIndex → ℚ) (g : Germ) :
    directedCurrent (faceGradient r) g = r (leftFace g) - r (rightFace g) := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [directedCurrent,faceGradient,dartSign,edgeOf,canonicalDart,upEnd,
      leftFace,rightFace,reverseGerm,neighbor]

theorem gradient_conserved (r : FaceIndex → ℚ) : ConservedCurrent (faceGradient r) := by
  intro v
  simp only [directedCurrent_gradient]
  cases v <;> simp [Fin.sum_univ_succ,leftFace,rightFace,reverseGerm,neighbor] <;> ring

theorem finite_gradient_injective (r s : FaceIndex →₀ ℚ)
    (h : faceGradient r = faceGradient s) : r = s := by
  have hh (i j : ℤ) : r (i+1,j) - s (i+1,j) = r (i,j) - s (i,j) := by
    have he := congrFun h ((i+1,j),0)
    simp [faceGradient,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] at he
    linarith
  ext a
  rcases a with ⟨i,j⟩
  let k : ℤ := -(QFlow.faceRadius r : ℤ) - QFlow.faceRadius s - 1
  have hr : r (k,j) = 0 := by
    by_contra hz
    have hb := (QFlow.mem_support_in_box r (k,j) (Finsupp.mem_support_iff.mpr hz)).1
    dsimp [k] at hb
    omega
  have hs : s (k,j) = 0 := by
    by_contra hz
    have hb := (QFlow.mem_support_in_box s (k,j) (Finsupp.mem_support_iff.mpr hz)).1
    dsimp [k] at hb
    omega
  have he := QFlow.int_function_constant (f := fun i => r (i,j) - s (i,j)) (fun i => hh i j) i k
  rw [hr,hs] at he
  linarith

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def rationalFlowComponent (q : EdgeIndex →₀ ℚ) (k : Fin 3) : FaceIndex →₀ ℚ :=
  Finsupp.comapDomain (fun a => (a,k)) q (by intro a _ b _ h; exact (Prod.mk.inj h).1)

theorem conserved_finite_potential (q : EdgeIndex →₀ ℚ) (hq : ConservedCurrent q) :
    ∃ r : FaceIndex →₀ ℚ, faceGradient r = q := by
  let q' : QFlow.FiniteHoneycombFlow := {
    q0 := rationalFlowComponent q 0
    q1 := rationalFlowComponent q 1
    q2 := rationalFlowComponent q 2
    up_conservation := by
      intro i j
      change q ((i,j),0) + q ((i,j),1) + q ((i,j),2) = 0
      simpa [directedCurrent,dartSign,edgeOf,Fin.sum_univ_succ,add_assoc] using hq (.up i j)
    down_conservation := by
      intro i j
      have h := hq (.down i j)
      simp [directedCurrent,dartSign,edgeOf,Fin.sum_univ_succ] at h
      change q ((i,j+1),0) + q ((i,j),1) + q ((i+1,j),2) = 0
      linarith }
  obtain ⟨r,hr⟩ := QFlow.finite_flow_is_face_boundary q'
  refine ⟨r,?_⟩
  funext e
  rcases e with ⟨⟨i,j⟩,k⟩
  have h := hr i j
  change q ((i,j),0) = _ ∧ q ((i,j),1) = _ ∧ q ((i,j),2) = _ at h
  fin_cases k <;>
    simp [faceGradient,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] <;>
    tauto

theorem potential_supported_on_cycle_cells (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0)
    (r : FaceIndex →₀ ℚ)
    (hr : ∀ e, e ∉ cellEdges p.support → faceGradient r e = 0) :
    r.support ⊆ p.support := by
  classical
  let pQ : FaceIndex →₀ ℚ := p.mapRange (fun x : ℤ => (x : ℚ)) (by norm_num)
  let rOut : FaceIndex →₀ ℚ := r.filter (fun a => p a = 0)
  have hpQ (e : EdgeIndex) : faceGradient pQ e = (wordFlow g w e : ℚ) := by
    have h := hp (canonicalDart e)
    rcases e with ⟨⟨i,j⟩,k⟩
    simp only [canonicalDart,upEnd,orientedFlow_up] at h
    simp only [faceGradient,pQ,Finsupp.mapRange_apply]
    exact_mod_cast h.symm
  have hOut : ∀ e, wordFlow g w e = 0 → faceGradient rOut e = 0 := by
    intro e he
    have hpE := hp (canonicalDart e)
    have hz : p (leftFace (canonicalDart e)) = p (rightFace (canonicalDart e)) := by
      rcases e with ⟨⟨i,j⟩,k⟩
      simp only [canonicalDart,upEnd,orientedFlow_up,he] at hpE
      simp only [canonicalDart,upEnd]
      omega
    by_cases hl : p (leftFace (canonicalDart e)) = 0
    · have hrz : p (rightFace (canonicalDart e)) = 0 := hz ▸ hl
      have hout : e ∉ cellEdges p.support := by
        simp [mem_cellEdges,Finsupp.mem_support_iff,hl,hrz]
      simpa [faceGradient,rOut,Finsupp.filter_apply,hl,hrz] using hr e hout
    · have hrz : p (rightFace (canonicalDart e)) ≠ 0 := hz ▸ hl
      simp [faceGradient,rOut,hl,hrz]
  obtain ⟨c,hc'⟩ := simple_cycle_current_scalar g w hN hc
    (faceGradient rOut) (gradient_conserved rOut) hOut
  have hEq : rOut = c • pQ := by
    apply finite_gradient_injective
    funext e
    rw [hc' e,← hpQ e]
    simp only [faceGradient,Finsupp.smul_apply,smul_eq_mul]
    ring
  obtain ⟨a,ha⟩ := Finsupp.support_nonempty_iff.mpr hpne
  have hpa : p a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hpQa : pQ a ≠ 0 := by
    simpa only [pQ,Finsupp.mapRange_apply,ne_eq,Int.cast_eq_zero] using hpa
  have hval := congrArg (fun f : FaceIndex →₀ ℚ => f a) hEq
  simp only [rOut,Finsupp.filter_apply,ite_eq_right hpa,Finsupp.smul_apply,smul_eq_mul] at hval
  have hcz : c = 0 := (mul_eq_zero.mp hval.symm).resolve_right hpQa
  have hR : rOut = 0 := by simpa [hcz] using hEq
  intro a ha
  by_contra hnot
  have hpz : p a = 0 := by simpa only [Finsupp.mem_support_iff,not_not] using hnot
  have hz := congrArg (fun f : FaceIndex →₀ ℚ => f a) hR
  simp only [rOut,Finsupp.filter_apply,ite_eq_left hpz,Finsupp.zero_apply] at hz
  exact (Finsupp.mem_support_iff.mp ha) hz



theorem edge_mem_around (S : Finset FaceIndex) (g : Germ) :
    edgeOf g ∈ cellEdges S ↔ leftFace g ∈ S ∨ rightFace g ∈ S := by
  rw [mem_cellEdges]
  rcases canonicalDart_edgeOf g with h | h
  · rw [h]
  · rw [h,rightFace_reverse]
    change rightFace g ∈ S ∨ leftFace g ∈ S ↔ _
    exact or_comm

theorem incident_faces_equal (p : FaceIndex →₀ ℤ) (v : Vertex)
    (hp : ∀ k : Fin 3, p (leftFace (v,k)) = p (rightFace (v,k)))
    (k l : Fin 3) : p (leftFace (v,k)) = p (leftFace (v,l)) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  cases v <;> fin_cases k <;> fin_cases l <;>
    simp [leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

theorem nonboundary_vertex_all_edges (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (v : Vertex) (hv : v ∈ cellVertices p.support) (hnot : v ∉ traced g w)
    (k : Fin 3) : edgeOf (v,k) ∈ cellEdges p.support := by
  have hzero (l : Fin 3) : orientedFlow (wordFlow g w) (v,l) = 0 := by
    rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
    exact turnVisit_eq_zero_of_not_mem g w v l hnot
  have he (l : Fin 3) : p (leftFace (v,l)) = p (rightFace (v,l)) := by
    have hh := hp (v,l)
    rw [hzero l] at hh
    omega
  obtain ⟨l,hl⟩ := (mem_cellVertices p.support v).mp hv
  rw [edge_mem_around]
  apply Or.inl
  rw [Finsupp.mem_support_iff] at hl ⊢
  rwa [incident_faces_equal p v he k l]

theorem finite_vertex_flat_zero (f : Vertex →₀ ℚ)
    (hf : ∀ v k, f (neighbor v k) = f v) : f = 0 := by
  classical
  let row : Vertex → ℤ := fun v => match v with | .up _ j => j | .down _ j => j
  let M : ℕ := f.support.sup fun v => (row v).natAbs
  have hu (i j : ℤ) : f (.up i j) = 0 := by
    have hh (k : ℤ) : f (.up i (k+1)) = f (.up i k) := by
      have h0 := hf (.down i k) 0
      have h1 := hf (.down i k) 1
      simp only [neighbor,↓reduceIte,Fin.isValue] at h0 h1
      exact h0.trans h1.symm
    let k : ℤ := (M : ℤ) + 1
    have he := QFlow.int_function_constant (f := fun j => f (.up i j)) hh j k
    rw [he]
    by_contra hk
    have hb : (row (.up i k)).natAbs ≤ M :=
      Finset.le_sup (f := fun v : Vertex => (row v).natAbs)
        (Finsupp.mem_support_iff.mpr hk)
    dsimp [row,k] at hb
    omega
  ext v
  cases v with
  | up i j => exact hu i j
  | down i j =>
      have h := hf (.down i j) 1
      simpa [neighbor,hu] using h.symm

theorem flat_along_dart (S : Finset FaceIndex) (f : Vertex → ℚ)
    (hf : ∀ e ∈ cellEdges S, f (upEnd e) = f (downEnd e))
    (g : Germ) (h : edgeOf g ∈ cellEdges S) : f (neighbor g.1 g.2) = f g.1 := by
  have he := hf (edgeOf g) h
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [edgeOf,upEnd,downEnd,neighbor] at he ⊢ <;> first | exact he.symm | exact he

theorem cell_flat_zero_boundary (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (f : Vertex →₀ ℚ) (hS : f.support ⊆ cellVertices p.support)
    (hflat : ∀ e ∈ cellEdges p.support, f (upEnd e) = f (downEnd e))
    (hbd : ∀ v ∈ traced g w, f v = 0) : f = 0 := by
  apply finite_vertex_flat_zero
  intro v k
  by_cases he : edgeOf (v,k) ∈ cellEdges p.support
  · exact flat_along_dart _ f hflat (v,k) he
  · have hz (d : Germ) (h : edgeOf d ∉ cellEdges p.support) : f d.1 = 0 := by
      by_cases hV : d.1 ∈ cellVertices p.support
      · apply hbd
        by_contra hnot
        exact h (nonboundary_vertex_all_edges g w hc p hp d.1 hV hnot d.2)
      · by_contra hne
        exact hV (hS (Finsupp.mem_support_iff.mpr hne))
    rw [hz (v,k) he]
    exact hz (reverseGerm (v,k)) (by simpa using he)

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem cell_euler_of_exact {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [Nonempty V]
    (A : Matrix V E ℚ) (B : (F → ℚ) →ₗ[ℚ] (E → ℚ))
    (hB : Function.Injective B) (hex : B.range = A.mulVecLin.ker)
    (hconst : A.transpose.mulVecLin.ker = Submodule.span ℚ {(1 : V → ℚ)}) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F = 1 := by
  have hF : Module.finrank ℚ A.mulVecLin.ker = Fintype.card F := by
    rw [← hex,LinearMap.finrank_range_of_inj hB,Module.finrank_fintype_fun_eq_card]
  have hV : Module.finrank ℚ A.transpose.mulVecLin.ker = 1 := by
    rw [hconst]
    exact finrank_span_singleton (by
      obtain ⟨v⟩ := ‹Nonempty V›
      intro h
      have := congrFun h v
      norm_num at this)
  have hrE := A.mulVecLin.finrank_range_add_finrank_ker
  have hrV := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr := A.rank_transpose
  change Module.finrank ℚ A.transpose.mulVecLin.range =
    Module.finrank ℚ A.mulVecLin.range at hr
  rw [hF,Module.finrank_fintype_fun_eq_card] at hrE
  rw [hV,Module.finrank_fintype_fun_eq_card] at hrV
  omega

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def extendOn {α : Type*} [DecidableEq α] (S : Finset α) (f : S → ℚ) : α →₀ ℚ :=
  Finsupp.onFinset S (fun a => if ha : a ∈ S then f ⟨a,ha⟩ else 0)
    (by intro a h; by_contra ha; simp [ha] at h)

@[simp] theorem extendOn_apply_mem {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) (a : S) : extendOn S f a = f a := by
  simp [extendOn]

@[simp] theorem extendOn_apply_not_mem {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) (a : α) (ha : a ∉ S) : extendOn S f a = 0 := by
  simp [extendOn,ha]

theorem extendOn_support {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) : (extendOn S f).support ⊆ S := by
  intro a ha
  by_contra h
  exact (Finsupp.mem_support_iff.mp ha) (extendOn_apply_not_mem S f a h)

theorem extendOn_injective {α : Type*} [DecidableEq α] (S : Finset α) :
    Function.Injective (extendOn S) := by
  intro f g h
  funext a
  have he := congrArg (fun t : α →₀ ℚ => t a) h
  simpa using he

theorem extendOn_restrict {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α →₀ ℚ) (h : f.support ⊆ S) : extendOn S (fun a => f a) = f := by
  ext a
  by_cases ha : a ∈ S
  · exact extendOn_apply_mem S (fun a => f a) ⟨a,ha⟩
  · rw [extendOn_apply_not_mem S _ a ha]
    by_contra hf
    exact ha (h (Finsupp.mem_support_iff.mpr (Ne.symm hf)))

noncomputable def rationalBoundary : (EdgeIndex →₀ ℚ) →+ (Vertex →₀ ℚ) :=
  Finsupp.liftAddHom fun e => Finsupp.singleAddHom (upEnd e) - Finsupp.singleAddHom (downEnd e)

@[simp] theorem rationalBoundary_single (e : EdgeIndex) (a : ℚ) :
    rationalBoundary (Finsupp.single e a) =
      Finsupp.single (upEnd e) a - Finsupp.single (downEnd e) a := by
  simp [rationalBoundary]

theorem rationalBoundary_up (q : EdgeIndex →₀ ℚ) (i j : ℤ) :
    rationalBoundary q (.up i j) = q ((i,j),0) + q ((i,j),1) + q ((i,j),2) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      fin_cases k <;>
        simp [rationalBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem rationalBoundary_down (q : EdgeIndex →₀ ℚ) (i j : ℤ) :
    rationalBoundary q (.down i j) =
      -(q ((i,j+1),0) + q ((i,j),1) + q ((i+1,j),2)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      have hy : j = y - 1 ↔ y = j + 1 := by omega
      have hx : i = x - 1 ↔ x = i + 1 := by omega
      fin_cases k <;>
        simp [rationalBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

theorem rationalBoundary_apply (q : EdgeIndex →₀ ℚ) (v : Vertex) :
    rationalBoundary q v = ∑ k : Fin 3, directedCurrent q (v,k) := by
  cases v <;> simp [rationalBoundary_up,rationalBoundary_down,Fin.sum_univ_succ,
    directedCurrent,dartSign,edgeOf] <;> ring

theorem rationalBoundary_eq_zero (q : EdgeIndex →₀ ℚ) :
    rationalBoundary q = 0 ↔ ConservedCurrent q := by
  simp only [ConservedCurrent,← rationalBoundary_apply,DFunLike.ext_iff,Finsupp.zero_apply]

noncomputable def incidenceMatrix (S : Finset FaceIndex) :
    Matrix (cellVertices S) (cellEdges S) ℚ :=
  fun v e => (if v.1 = upEnd e then 1 else 0) - (if v.1 = downEnd e then 1 else 0)

theorem cell_upEnd (S : Finset FaceIndex) (e : cellEdges S) : upEnd e ∈ cellVertices S := by
  apply edge_mem_vertex S (canonicalDart e)
  have h : edgeOf (canonicalDart e) = e := by
    rcases e with ⟨⟨⟨i,j⟩,k⟩,he⟩
    rfl
  rw [h]
  exact e.property

theorem cell_downEnd (S : Finset FaceIndex) (e : cellEdges S) : downEnd e ∈ cellVertices S := by
  apply edge_mem_neighbor S (canonicalDart e)
  have h : edgeOf (canonicalDart e) = e := by
    rcases e with ⟨⟨⟨i,j⟩,k⟩,he⟩
    rfl
  rw [h]
  exact e.property

theorem transpose_incidence_apply (S : Finset FaceIndex) (f : cellVertices S → ℚ)
    (e : cellEdges S) :
    (incidenceMatrix S).transpose.mulVec f e =
      f ⟨upEnd e,cell_upEnd S e⟩ - f ⟨downEnd e,cell_downEnd S e⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incidenceMatrix, sub_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single ⟨upEnd e,cell_upEnd S e⟩]
    · simp
    · intro b _ hb
      have h : b.1 ≠ upEnd e := fun h => hb (Subtype.ext h)
      simp [h]
    · simp
  · rw [Finset.sum_eq_single ⟨downEnd e,cell_downEnd S e⟩]
    · simp
    · intro b _ hb
      have h : b.1 ≠ downEnd e := fun h => hb (Subtype.ext h)
      simp [h]
    · simp

@[simp] theorem extendOn_add {α : Type*} [DecidableEq α] (S : Finset α)
    (f g : S → ℚ) : extendOn S (f + g) = extendOn S f + extendOn S g := by
  ext a
  by_cases ha : a ∈ S <;> simp [extendOn,ha]

@[simp] theorem extendOn_smul {α : Type*} [DecidableEq α] (S : Finset α)
    (c : ℚ) (f : S → ℚ) : extendOn S (c • f) = c • extendOn S f := by
  ext a
  by_cases ha : a ∈ S <;> simp [extendOn,ha]

theorem extendOn_eq_sum {α : Type*} [DecidableEq α] (S : Finset α) (f : S → ℚ) :
    extendOn S f = ∑ a : S, Finsupp.single a.1 (f a) := by
  ext a
  by_cases ha : a ∈ S
  · change extendOn S f (⟨a,ha⟩ : S) = _
    rw [extendOn_apply_mem,Finsupp.finsetSum_apply,Finset.sum_eq_single (⟨a,ha⟩ : S)]
    · simp
    · intro b _ hb
      have h : b.1 ≠ a := fun h => hb (Subtype.ext h)
      simp [h]
    · simp
  · rw [extendOn_apply_not_mem S f a ha,Finsupp.finsetSum_apply]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hb : b.1 ≠ a := fun h => ha (h ▸ b.property)
    simp [hb]

theorem incidence_apply (S : Finset FaceIndex) (q : cellEdges S → ℚ)
    (v : cellVertices S) :
    (incidenceMatrix S).mulVec q v = rationalBoundary (extendOn (cellEdges S) q) v := by
  rw [extendOn_eq_sum,map_sum,Finsupp.finsetSum_apply]
  simp only [Matrix.mulVec,dotProduct,incidenceMatrix,rationalBoundary_single,
    Finsupp.sub_apply,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro e _
  simp only [sub_mul,ite_mul,one_mul,zero_mul,eq_comm]

theorem rationalBoundary_support_cells (S : Finset FaceIndex) (q : EdgeIndex →₀ ℚ)
    (hS : q.support ⊆ cellEdges S) : (rationalBoundary q).support ⊆ cellVertices S := by
  intro v hv
  by_contra hV
  apply (Finsupp.mem_support_iff.mp hv)
  rw [rationalBoundary_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hz : q (edgeOf (v,k)) = 0 := by
    by_contra he
    exact hV (edge_mem_vertex S (v,k) (hS (Finsupp.mem_support_iff.mpr he)))
  simp [directedCurrent,hz]

theorem incidence_zero_iff (S : Finset FaceIndex) (q : cellEdges S → ℚ) :
    (incidenceMatrix S).mulVec q = 0 ↔ ConservedCurrent (extendOn (cellEdges S) q) := by
  rw [← rationalBoundary_eq_zero]
  constructor
  · intro h
    ext v
    by_cases hv : v ∈ cellVertices S
    · have he := congrFun h ⟨v,hv⟩
      simpa only [incidence_apply,Pi.zero_apply,Finsupp.zero_apply] using he
    · change rationalBoundary _ v = 0
      by_contra he
      exact hv (rationalBoundary_support_cells S _ (extendOn_support _ _)
        (Finsupp.mem_support_iff.mpr he))
  · intro h
    funext v
    rw [incidence_apply,h]
    rfl

theorem gradient_zero_off_cells (S : Finset FaceIndex) (r : FaceIndex →₀ ℚ)
    (hr : r.support ⊆ S) (e : EdgeIndex) (he : e ∉ cellEdges S) :
    faceGradient r e = 0 := by
  rw [mem_cellEdges,not_or] at he
  have hz (a : FaceIndex) (ha : a ∉ S) : r a = 0 := by
    by_contra h
    exact ha (hr (Finsupp.mem_support_iff.mpr h))
  simp [faceGradient,hz _ he.1,hz _ he.2]

noncomputable def cellFaceBoundary (S : Finset FaceIndex) :
    (S → ℚ) →ₗ[ℚ] (cellEdges S → ℚ) where
  toFun f e := faceGradient (extendOn S f) e
  map_add' f g := by
    funext e
    simp [extendOn_add,faceGradient]
    ring
  map_smul' c f := by
    funext e
    simp [extendOn_smul,faceGradient]
    ring

theorem extend_faceBoundary (S : Finset FaceIndex) (f : S → ℚ) :
    (extendOn (cellEdges S) (cellFaceBoundary S f) : EdgeIndex → ℚ) =
      faceGradient (extendOn S f) := by
  funext e
  by_cases he : e ∈ cellEdges S
  · exact extendOn_apply_mem _ _ ⟨e,he⟩
  · rw [extendOn_apply_not_mem _ _ _ he,
      gradient_zero_off_cells S _ (extendOn_support _ _) e he]

theorem cellFaceBoundary_injective (S : Finset FaceIndex) :
    Function.Injective (cellFaceBoundary S) := by
  intro f g h
  apply extendOn_injective S
  apply finite_gradient_injective
  rw [← extend_faceBoundary,← extend_faceBoundary,h]

theorem cellFaceBoundary_range (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0) :
    (cellFaceBoundary p.support).range = (incidenceMatrix p.support).mulVecLin.ker := by
  ext q
  change (∃ f,cellFaceBoundary p.support f = q) ↔ (incidenceMatrix p.support).mulVec q = 0
  rw [incidence_zero_iff]
  constructor
  · rintro ⟨f,rfl⟩
    rw [extend_faceBoundary]
    exact gradient_conserved _
  · intro hq
    obtain ⟨r,hr⟩ := conserved_finite_potential _ hq
    have hS : r.support ⊆ p.support := by
      apply potential_supported_on_cycle_cells g w hN hc p hp hpne r
      intro e he
      rw [hr]
      exact extendOn_apply_not_mem _ _ _ he
    refine ⟨fun a => r a,?_⟩
    funext e
    change faceGradient (extendOn p.support (fun a => r a)) e = q e
    rw [extendOn_restrict _ r hS,hr]
    exact extendOn_apply_mem _ _ e

theorem represented_nonzero_edge_mem (S : Finset FaceIndex) (p : FaceIndex →₀ ℤ)
    (hS : p.support ⊆ S) (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (hg : orientedFlow q g ≠ 0) : edgeOf g ∈ cellEdges S := by
  rw [edge_mem_around]
  have h := hp g
  by_contra hn
  simp only [not_or] at hn
  have hz (a : FaceIndex) (ha : a ∉ S) : p a = 0 := by
    by_contra h
    exact ha (hS (Finsupp.mem_support_iff.mpr h))
  rw [hz _ hn.1,hz _ hn.2,sub_self] at h
  exact hg h

theorem contour_outgoing_nonzero (q : EdgeIndex →₀ ℤ) (g : Germ) (b : Bool)
    (h : LocalContour q g b) : orientedFlow q (g.1,outgoingSlot g b) ≠ 0 := by
  have hk : outgoingSlot g b ≠ g.2 := by
    rcases g with ⟨v,k⟩
    fin_cases k <;> cases b <;> simp [outgoingSlot]
  rw [h (outgoingSlot g b)]
  simp [hk]

theorem contour_step_mem (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (b : Bool) (h : LocalContour q g b) :
    edgeOf (g.1,outgoingSlot g b) ∈ cellEdges p.support := by
  exact represented_nonzero_edge_mem _ p (Finset.Subset.refl _) q hp _
    (contour_outgoing_nonzero q g b h)

theorem contour_flat_trace (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (f : Vertex → ℚ)
    (hf : ∀ e ∈ cellEdges p.support, f (upEnd e) = f (downEnd e))
    (g : Germ) (w : List Bool) (hw : WordContour q g w) :
    ∀ v ∈ traced g w, v ∈ cellVertices p.support ∧ f v = f g.1 := by
  induction w generalizing g with
  | nil => simp [traced]
  | cons b w ih =>
      have hE := contour_step_mem p q hp g b hw.1
      have hV := edge_mem_vertex _ _ hE
      have hs : f (advance g b).1 = f g.1 :=
        flat_along_dart _ f hf (g.1,outgoingSlot g b) hE
      simp only [traced,List.mem_cons]
      intro v hv
      rcases hv with rfl | hv
      · exact ⟨hV,rfl⟩
      · obtain ⟨hv',hf'⟩ := ih (advance g b) hw.2 v hv
        exact ⟨hv',hf'.trans hs⟩

theorem cycle_vertices_nonempty (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) :
    g.1 ∈ cellVertices p.support := by
  obtain ⟨b,w,rfl⟩ := List.exists_cons_of_ne_nil hne
  have h := (simple_closed_word_contour g (b::w) hN hc).1
  exact edge_mem_vertex _ (g.1,outgoingSlot g b) (contour_step_mem p _ hp g b h)

theorem transpose_incidence_kernel (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) :
    (incidenceMatrix p.support).transpose.mulVecLin.ker =
      Submodule.span ℚ {(1 : cellVertices p.support → ℚ)} := by
  have hg : g.1 ∈ cellVertices p.support := cycle_vertices_nonempty g w hne hN hc p hp
  ext f
  change (incidenceMatrix p.support).transpose.mulVec f = 0 ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    let fhat := extendOn (cellVertices p.support) f
    have hflat : ∀ e ∈ cellEdges p.support, fhat (upEnd e) = fhat (downEnd e) := by
      intro e he
      have heq := congrFun h ⟨e,he⟩
      rw [transpose_incidence_apply] at heq
      have h1 := cell_upEnd p.support (⟨e,he⟩ : cellEdges p.support)
      have h2 := cell_downEnd p.support (⟨e,he⟩ : cellEdges p.support)
      simpa only [fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left h1,dite_eq_left h2] using
        sub_eq_zero.mp heq
    have htrace := contour_flat_trace p (wordFlow g w) hp fhat hflat g w
      (simple_closed_word_contour g w hN hc)
    let c : ℚ := fhat g.1
    let diff : Vertex →₀ ℚ := extendOn (cellVertices p.support) (fun a => f a - c)
    have hdiff (a : cellVertices p.support) : diff a = f a - c :=
      extendOn_apply_mem _ _ a
    have hd : diff = 0 := by
      apply cell_flat_zero_boundary g w hc p hp diff (extendOn_support _ _)
      · intro e he
        have h1 := cell_upEnd p.support (⟨e,he⟩ : cellEdges p.support)
        have h2 := cell_downEnd p.support (⟨e,he⟩ : cellEdges p.support)
        have he' := congrArg (fun x : ℚ => x-c) (hflat e he)
        simpa only [diff,fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left h1,dite_eq_left h2] using he'
      · intro v hv
        obtain ⟨hv',he⟩ := htrace v hv
        change fhat v = c at he
        have he' : f ⟨v,hv'⟩ = c := by
          simpa only [fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left hv'] using he
        simp only [diff,extendOn,Finsupp.onFinset_apply,dite_eq_left hv',he',sub_self]
    refine ⟨c,?_⟩
    funext a
    have he := congrArg (fun z : Vertex →₀ ℚ => z a) hd
    simp only [diff,extendOn,Finsupp.onFinset_apply,dite_eq_left a.property,Finsupp.zero_apply] at he
    simpa only [Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one] using (sub_eq_zero.mp he).symm
  · rintro ⟨c,rfl⟩
    funext e
    rw [transpose_incidence_apply]
    simp

theorem simple_cycle_cell_euler (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0) :
    ((cellVertices p.support).card : ℤ) - (cellEdges p.support).card + p.support.card = 1 := by
  have : Nonempty (cellVertices p.support) :=
    ⟨⟨g.1,cycle_vertices_nonempty g w hne hN hc p hp⟩⟩
  simpa using cell_euler_of_exact (incidenceMatrix p.support) (cellFaceBoundary p.support)
    (cellFaceBoundary_injective _) (cellFaceBoundary_range g w hN hc p hp hpne)
    (transpose_incidence_kernel g w hne hN hc p hp)

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def turnUnit (b : Bool) : ℤ := if b then 1 else -1

def turnUnits (w : List Bool) : ℤ := (w.map turnUnit).sum

def faceCount (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  ∑ k : Fin 3, if leftFace (v,k) ∈ S then 1 else 0

def edgeCount (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  ∑ k : Fin 3, if edgeOf (v,k) ∈ cellEdges S then 1 else 0

def cellCurvature (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  6 - 3 * edgeCount S v + faceCount S v

@[simp] theorem rightFace_prev (v : Vertex) (k : Fin 3) :
    rightFace (v,k) = leftFace (v,k+2) := by
  cases v <;> fin_cases k <;> simp [rightFace,reverseGerm,neighbor,leftFace]

theorem leftFace_injective (v : Vertex) : Function.Injective (fun k : Fin 3 => leftFace (v,k)) := by
  intro k l h
  cases v <;> fin_cases k <;> fin_cases l <;> simp [leftFace] at h ⊢ <;> omega

theorem faceCount_incidence (S : Finset FaceIndex) (v : Vertex) :
    faceCount S v = ∑ a ∈ S, if v ∈ faceVertices a then (1 : ℤ) else 0 := by
  classical
  have hpair (a : FaceIndex) : (∑ k : Fin 3, if leftFace (v,k) = a then (1 : ℤ) else 0) =
      if v ∈ faceVertices a then 1 else 0 := by
    by_cases hv : v ∈ faceVertices a
    · obtain ⟨k,hk⟩ := (mem_faceVertices v a).mp hv
      rw [ite_eq_left hv,Finset.sum_eq_single k]
      · simp [hk]
      · intro l _ hl
        have hn : leftFace (v,l) ≠ a := fun h => hl (leftFace_injective v (h.trans hk.symm))
        simp [hn]
      · simp
    · rw [ite_eq_right hv]
      apply Finset.sum_eq_zero
      intro k _
      have hn : leftFace (v,k) ≠ a := fun h => hv ((mem_faceVertices v a).mpr ⟨k,h⟩)
      simp [hn]
  simp_rw [← hpair]
  rw [Finset.sum_comm]
  unfold faceCount
  apply Finset.sum_congr rfl
  intro k _
  simp

@[simp] theorem edgeOf_slot (g : Germ) : (edgeOf g).2 = g.2 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [edgeOf]

@[simp] theorem edgeOf_canonical (e : EdgeIndex) : edgeOf (canonicalDart e) = e := by
  rcases e with ⟨⟨i,j⟩,k⟩
  rfl

@[simp] theorem edgeOf_downEnd (e : EdgeIndex) : edgeOf (downEnd e,e.2) = e := by
  change edgeOf (reverseGerm (canonicalDart e)) = e
  rw [edgeOf_reverse,edgeOf_canonical]

theorem edgeOf_eq_iff (v : Vertex) (e : EdgeIndex) :
    edgeOf (v,e.2) = e ↔ v = upEnd e ∨ v = downEnd e := by
  constructor
  · intro h
    rcases canonicalDart_edgeOf (v,e.2) with h' | h'
    · rw [h] at h'
      exact Or.inl (congrArg Prod.fst h').symm
    · rw [h] at h'
      have he := congrArg (fun x : Germ => (reverseGerm x).1) h'
      simp only [reverseGerm_reverseGerm] at he
      exact Or.inr he.symm
  · rintro (rfl | rfl)
    · exact edgeOf_canonical e
    · exact edgeOf_downEnd e

theorem upEnd_ne_downEnd (e : EdgeIndex) : upEnd e ≠ downEnd e := by
  rcases e with ⟨⟨i,j⟩,k⟩
  fin_cases k <;> simp [upEnd,downEnd,neighbor]

theorem edgeCount_incidence (S : Finset FaceIndex) (v : Vertex) :
    edgeCount S v = ∑ e ∈ cellEdges S,
      ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ) := by
  classical
  have hpair (e : EdgeIndex) : (∑ k : Fin 3, if edgeOf (v,k) = e then (1 : ℤ) else 0) =
      (if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) := by
    rw [Finset.sum_eq_single e.2]
    · simp only [edgeOf_eq_iff]
      by_cases hu : v = upEnd e
      · simp [hu,upEnd_ne_downEnd]
      · by_cases hd : v = downEnd e
        · simp [hd, Ne.symm (upEnd_ne_downEnd e)]
        · simp [hu,hd]
    · intro k _ hk
      have hn : edgeOf (v,k) ≠ e := fun h => hk (by simpa using congrArg Prod.snd h)
      simp [hn]
    · simp
  simp_rw [← hpair]
  rw [Finset.sum_comm]
  unfold edgeCount
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem faceVertices_card (a : FaceIndex) : (faceVertices a).card = 6 := by
  rcases a with ⟨i,j⟩
  simp [faceVertices]

theorem sum_faceCount (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, faceCount S v = 6 * (S.card : ℤ) := by
  classical
  simp_rw [faceCount_incidence]
  rw [Finset.sum_comm]
  have ha (a : FaceIndex) (hma : a ∈ S) :
      (∑ v ∈ cellVertices S, if v ∈ faceVertices a then (1 : ℤ) else 0) = 6 := by
    rw [← Finset.sum_filter]
    have hF : (cellVertices S).filter (fun v => v ∈ faceVertices a) = faceVertices a := by
      ext v
      simp only [Finset.mem_filter,and_iff_right_iff_imp]
      intro hv
      exact Finset.mem_biUnion.mpr ⟨a,hma,hv⟩
    rw [hF]
    simp [faceVertices_card]
  simp_rw [Finset.sum_congr rfl ha]
  simp [mul_comm]

theorem sum_edgeCount (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, edgeCount S v = 2 * ((cellEdges S).card : ℤ) := by
  classical
  simp_rw [edgeCount_incidence]
  rw [Finset.sum_comm]
  have he (e : EdgeIndex) (hme : e ∈ cellEdges S) :
      (∑ v ∈ cellVertices S,
        ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ)) = 2 := by
    have hu : upEnd e ∈ cellVertices S :=
      edge_mem_vertex S (canonicalDart e) (by simpa using hme)
    have hd : downEnd e ∈ cellVertices S :=
      edge_mem_neighbor S (canonicalDart e) (by simpa using hme)
    rw [Finset.sum_add_distrib]
    simp [hu,hd]
  simp_rw [Finset.sum_congr rfl he]
  simp [mul_comm]

theorem sum_cellCurvature (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, cellCurvature S v =
      6 * ((cellVertices S).card - (cellEdges S).card + (S.card : ℤ)) := by
  simp only [cellCurvature,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,sum_faceCount,sum_edgeCount]
  simp
  ring

theorem numeric_contour_curvature (f : Fin 3 → ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hf : ∀ l, f l = 0 ∨ f l = ε)
    (k : Fin 3) (b : Bool)
    (h : ∀ l : Fin 3, f l - f (l+2) =
      (if l = k + (if b then 2 else 1) then 1 else 0) - (if l = k then 1 else 0)) :
    6 - 3 * (∑ l : Fin 3, if f l ≠ 0 ∨ f (l+2) ≠ 0 then (1 : ℤ) else 0) +
      (∑ l : Fin 3, if f l ≠ 0 then (1 : ℤ) else 0) = ε * turnUnit b := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hf0 := hf 0
  have hf1 := hf 1
  have hf2 := hf 2
  clear h hf
  rcases hε with rfl | rfl <;> fin_cases k <;> cases b <;>
    rcases hf0 with hf0 | hf0 <;> rcases hf1 with hf1 | hf1 <;>
    rcases hf2 with hf2 | hf2 <;>
    simp only [Fin.sum_univ_succ] at * <;> simp_all [turnUnit]

theorem contour_cellCurvature (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (b : Bool) (hw : LocalContour q g b) :
    cellCurvature p.support g.1 = ε * turnUnit b := by
  let f : Fin 3 → ℤ := fun l => p (leftFace (g.1,l))
  have hlocal (l : Fin 3) : f l - f (l+2) =
      (if l = g.2 + (if b then 2 else 1) then 1 else 0) - (if l = g.2 then 1 else 0) := by
    have h := (hp (g.1,l)).symm.trans (hw l)
    simp only [f,rightFace_prev,outgoingSlot] at h ⊢
    exact h
  have he := numeric_contour_curvature f ε hε (fun l => hvals _) g.2 b hlocal
  unfold cellCurvature edgeCount faceCount
  simp_rw [edge_mem_around,Finsupp.mem_support_iff,rightFace_prev]
  exact he

theorem nonboundary_cellCurvature (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) (p : FaceIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) (v : Vertex)
    (hv : v ∈ cellVertices p.support) (hnot : v ∉ traced g w) :
    cellCurvature p.support v = 0 := by
  have hE := nonboundary_vertex_all_edges g w hc p hp v hv hnot
  have hz (l : Fin 3) : orientedFlow (wordFlow g w) (v,l) = 0 := by
    rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
    exact turnVisit_eq_zero_of_not_mem g w v l hnot
  have he (l : Fin 3) : p (leftFace (v,l)) = p (rightFace (v,l)) := by
    have h := hp (v,l)
    rw [hz l] at h
    omega
  obtain ⟨l,hl⟩ := (mem_cellVertices _ v).mp hv
  have hF (k : Fin 3) : leftFace (v,k) ∈ p.support := by
    rw [Finsupp.mem_support_iff] at hl ⊢
    rwa [incident_faces_equal p v he k l]
  simp [cellCurvature,edgeCount,faceCount,hE,hF]

theorem contour_curvature_sum (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (w : List Bool) (hw : WordContour q g w) :
    ((traced g w).map (cellCurvature p.support)).sum = ε * turnUnits w := by
  induction w generalizing g with
  | nil => simp [traced,turnUnits]
  | cons b w ih =>
      simp only [traced,List.map_cons,List.sum_cons,turnUnits,List.map_cons,List.sum_cons]
      rw [contour_cellCurvature p ε hε hvals q hp g b hw.1,ih _ hw.2]
      simp only [turnUnits]
      ring

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def SimplePolygonTurning : Prop := ∀ (g : Germ) (w : List Bool),
  w ≠ [] → (traced g w).Nodup → terminalGerm g w = g →
    turnUnits w = 6 ∨ turnUnits w = -6

theorem simple_polygon_signed_turn (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (ε : ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (hpne : p ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hvals : ∀ a, p a = 0 ∨ p a = ε) : ε * turnUnits w = 6 := by
  have hEuler := simple_cycle_cell_euler g w hne hN hc p hp hpne
  have hw := simple_closed_word_contour g w hN hc
  have hsub : (traced g w).toFinset ⊆ cellVertices p.support := by
    intro v hv
    exact (contour_flat_trace p (wordFlow g w) hp (fun _ => 0)
      (by intros; rfl) g w hw v (List.mem_toFinset.mp hv)).1
  have hsum : (∑ v ∈ cellVertices p.support,cellCurvature p.support v) = ε * turnUnits w := by
    calc
      _ = ∑ v ∈ (traced g w).toFinset,cellCurvature p.support v := by
        symm
        apply Finset.sum_subset hsub
        intro v hv hnot
        exact nonboundary_cellCurvature g w hc p hp v hv
          (by simpa only [List.mem_toFinset] using hnot)
      _ = ((traced g w).map (cellCurvature p.support)).sum := List.sum_toFinset _ hN
      _ = _ := contour_curvature_sum p ε hε hvals (wordFlow g w) hp g w hw
  rw [sum_cellCurvature,hEuler,mul_one] at hsum
  exact hsum.symm

theorem simple_polygon_turning : SimplePolygonTurning := by
  intro g w hne hN hc
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g w hne hN hc
  have hsum := simple_polygon_signed_turn g w hne hN hc p ε hp hpne hε hvals
  rcases hε with rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)


def IsPolygon (E : Finset EdgeIndex) : Prop := ∃ (g : Germ) (w : List Bool),
  w ≠ [] ∧ (traced g w).Nodup ∧ terminalGerm g w = g ∧ (wordFlow g w).support = E

abbrev Polygon := { E : Finset EdgeIndex // IsPolygon E }

namespace Polygon
noncomputable def germ (P : Polygon) : Germ := P.property.choose
noncomputable def turns (P : Polygon) : List Bool := P.property.choose_spec.choose

theorem traversal (P : Polygon) :
    P.turns ≠ [] ∧ (traced P.germ P.turns).Nodup ∧
    terminalGerm P.germ P.turns = P.germ ∧ (wordFlow P.germ P.turns).support = P.val :=
  P.property.choose_spec.choose_spec

theorem has_indicator (P : Polygon) :
    ∃ (p : FaceIndex →₀ ℤ) (ε : ℤ), RepresentsFlow p (wordFlow P.germ P.turns) ∧
      p ≠ 0 ∧ (ε = 1 ∨ ε = -1) ∧ ∀ a, p a = 0 ∨ p a = ε :=
  simple_closed_word_indicator P.germ P.turns P.traversal.1 P.traversal.2.1 P.traversal.2.2.1

noncomputable def potential (P : Polygon) : FaceIndex →₀ ℤ := P.has_indicator.choose
noncomputable def orientation (P : Polygon) : ℤ := P.has_indicator.choose_spec.choose

theorem potential_spec (P : Polygon) :
    RepresentsFlow P.potential (wordFlow P.germ P.turns) ∧ P.potential ≠ 0 ∧
    (P.orientation = 1 ∨ P.orientation = -1) ∧
    ∀ a, P.potential a = 0 ∨ P.potential a = P.orientation :=
  P.has_indicator.choose_spec.choose_spec

noncomputable def interiorFaces (P : Polygon) : Finset FaceIndex := P.potential.support

def vertices (P : Polygon) : Finset Vertex := P.val.biUnion fun e => {upEnd e,downEnd e}

noncomputable def interior (P : Polygon) : Finset Vertex :=
  cellVertices P.interiorFaces \ P.vertices

def length (P : Polygon) : ℕ := P.val.card

noncomputable def ccwTurn (P : Polygon) (v : Vertex) : ℝ :=
  Real.pi / 3 * (3 - 2 * (faceCount P.interiorFaces v : ℝ))
end Polygon

noncomputable def inducedEdges (D : Finset Vertex) : Finset EdgeIndex := by
  classical
  exact ((D.product Finset.univ).image edgeOf).filter fun e => upEnd e ∈ D ∧ downEnd e ∈ D

noncomputable def polygons (D : Finset Vertex) : Finset Polygon := by
  classical
  exact (inducedEdges D).powerset.subtype IsPolygon

def Filled (D : Finset Vertex) : Prop := ∀ P ∈ polygons D, P.interior ⊆ D

noncomputable def visitMass (D : Finset Vertex) (v : Vertex) : ℝ := (visitSum D v).re

noncomputable def excursionMass (D : Finset Vertex) (v : Vertex) : ℝ := by
  classical
  exact ∑ e ∈ excursions D, if v ∈ traced e.1 e.2 then criticalActivity ^ e.2.length else 0

noncomputable def polygonSystems (D : Finset Vertex) (f : FaceIndex) :
    Finset (Finset Polygon) := by
  classical
  exact (polygons D).powerset.filter fun S =>
    (S : Set Polygon).Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
    ∀ P ∈ S, f ∈ P.interiorFaces

noncomputable def faceNestingMass (D : Finset Vertex) (f : FaceIndex) : ℝ :=
  ∑ S ∈ polygonSystems D f, ∏ P ∈ S, 2 * criticalActivity ^ P.length

noncomputable def tilingCoordinate (k : Fin 3) (z : ℝ × ℝ) : ℝ :=
  if k = 0 then 2 * z.2 / Real.sqrt 3
  else if k = 1 then z.1 - z.2 / Real.sqrt 3 + 1 / 2
  else z.1 + z.2 / Real.sqrt 3 + 1 / 2

def AdmissiblyConvex (D : Finset Vertex) : Prop :=
  ∃ lo hi : Fin 3 → ℤ, ∀ v : Vertex, v ∈ D ↔ ∀ k : Fin 3,
    (lo k : ℝ) < tilingCoordinate k (position v) ∧
    tilingCoordinate k (position v) < (hi k : ℝ)

def FiniteVisitRecursion : Prop := ∀ (D : Finset Vertex) (v : Vertex), Filled D → v ∈ D →
  visitMass D v = 3 +
    (∑ P ∈ polygons D, if v ∈ P.vertices then
      2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) else 0) +
    (∑ P ∈ polygons D, if v ∈ P.interior then
      2 * criticalActivity ^ P.length * visitMass P.interior v else 0)

def FiniteVisitsTheorem : Prop := FiniteVisitRecursion ∧
  (∀ P : Polygon, 0 < 2 * criticalActivity ^ P.length ∧
    ∀ v ∈ P.vertices, 0 < 2 * criticalActivity ^ (P.length - 1) *
      (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)))) ∧
  (∀ D v, Filled D → v ∈ D → 3 ≤ visitMass D v) ∧
  (∀ D E v, Filled D → Filled E → D ⊆ E → v ∈ D → visitMass D v ≤ visitMass E v) ∧
  (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ D v, Filled D → v ∈ D →
    c * (∑ k : Fin 3, faceNestingMass D (leftFace (v,k))) ≤ visitMass D v ∧
    visitMass D v ≤ C * (∑ k : Fin 3, faceNestingMass D (leftFace (v,k)))) ∧
  (∀ D v, AdmissiblyConvex D → v ∈ D →
    Real.cos (3 * Real.pi / 8) * excursionMass D v ≤ visitMass D v ∧
    visitMass D v ≤ excursionMass D v)

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def unusedSlot (g : Germ) (b : Bool) : Fin 3 := outgoingSlot g (!b)

@[simp] theorem turnUnit_not (b : Bool) : turnUnit (!b) = -turnUnit b := by
  cases b <;> simp [turnUnit]

@[simp] theorem turnUnits_cons (b : Bool) (w : List Bool) :
    turnUnits (b :: w) = turnUnit b + turnUnits w := by
  simp [turnUnits]

@[simp] theorem turnUnits_reverse (w : List Bool) :
    turnUnits (reverseTurns w) = -turnUnits w := by
  simp [turnUnits,reverseTurns,List.map_map,Function.comp_def,List.sum_neg]

@[simp] theorem wordWeight_append (u w : List Bool) :
    wordWeight (u ++ w) = wordWeight u * wordWeight w := by
  simp [wordWeight]

theorem turnAngle_sum (w : List Bool) :
    (w.map turnAngle).sum = (Real.pi / 3) * (turnUnits w : ℝ) := by
  induction w with
  | nil => simp [turnUnits]
  | cons b w ih =>
      simp only [List.map_cons,List.sum_cons,ih,turnUnits_cons,Int.cast_add]
      cases b <;> simp [turnAngle,turnUnit] <;> ring

theorem wordWeight_turnUnits (w : List Bool) :
    wordWeight w = (criticalActivity : ℂ) ^ w.length *
      Complex.exp (((Real.pi / 8) * (turnUnits w : ℝ) : ℝ) * Complex.I) := by
  rw [wordWeight_physical,turnAngle_sum]
  congr 2
  push_cast
  ring

theorem collision_weights_conjugate (b : Bool) (w : List Bool) :
    wordWeight (b :: reverseTurns w) = starRingEnd ℂ (wordWeight ((!b) :: w)) := by
  rw [← wordWeight_reverse,reverseTurns_cons,Bool.not_not,wordWeight_append]
  simp [wordWeight,mul_comm]

theorem collision_weights_cos (b : Bool) (w : List Bool) :
    wordWeight ((!b) :: w) + wordWeight (b :: reverseTurns w) =
      (2 : ℂ) * (criticalActivity : ℂ) ^ (b :: w).length *
      (Real.cos (Real.pi / 8 * ((turnUnits (b :: w) - 2 * turnUnit b : ℤ) : ℝ)) : ℂ) := by
  rw [collision_weights_conjugate,wordWeight_turnUnits]
  have ht : turnUnits ((!b) :: w) = turnUnits (b :: w) - 2 * turnUnit b := by
    simp only [turnUnits_cons,turnUnit_not]
    ring
  rw [ht,Complex.exp_ofReal_mul_I]
  simp only [List.length_cons,map_mul,map_add,map_pow,Complex.conj_ofReal,
    map_mul,Complex.conj_I]
  ring

theorem numeric_unused_face (f : Fin 3 → ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hf : ∀ l, f l = 0 ∨ f l = ε)
    (k : Fin 3) (b : Bool)
    (h : ∀ l : Fin 3, f l - f (l+2) =
      (if l = k + (if b then 2 else 1) then 1 else 0) - (if l = k then 1 else 0)) :
    2 * f (k + (if !b then 2 else 1)) = ε - turnUnit b := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hf0 := hf 0
  have hf1 := hf 1
  have hf2 := hf 2
  clear h hf
  rcases hε with rfl | rfl <;> fin_cases k <;> cases b <;>
    simp [turnUnit] at * <;> omega

theorem contour_unused_face (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (b : Bool) (hw : LocalContour q g b) :
    2 * p (leftFace (g.1,unusedSlot g b)) = ε - turnUnit b := by
  let f : Fin 3 → ℤ := fun l => p (leftFace (g.1,l))
  have hl (l : Fin 3) : f l - f (l+2) =
      (if l = g.2 + (if b then 2 else 1) then 1 else 0) - (if l = g.2 then 1 else 0) := by
    have h := (hp (g.1,l)).symm.trans (hw l)
    simp only [f,rightFace_prev,outgoingSlot] at h ⊢
    exact h
  exact numeric_unused_face f ε hε (fun l => hvals _) g.2 b hl

def CollisionPhase : Prop := ∀ (g : Germ) (b : Bool) (w : List Bool)
  (p : FaceIndex →₀ ℤ) (ε : ℤ),
  (traced g (b :: w)).Nodup → terminalGerm g (b :: w) = g →
  RepresentsFlow p (wordFlow g (b :: w)) → p ≠ 0 →
  (ε = 1 ∨ ε = -1) → (∀ a, p a = 0 ∨ p a = ε) →
  wordWeight ((!b) :: w) + wordWeight (b :: reverseTurns w) =
    if p (leftFace (g.1,unusedSlot g b)) = 0 then 0
    else -2 * (criticalActivity : ℂ) ^ (b :: w).length

theorem collision_phase : CollisionPhase := by
  intro g b w p ε hN hc hp hpne hε hvals
  have ht := simple_polygon_signed_turn g (b :: w) (by simp) hN hc p ε hp hpne hε hvals
  have hf := contour_unused_face p ε hε hvals (wordFlow g (b :: w)) hp g b
    (simple_closed_word_contour g (b :: w) hN hc).1
  rw [collision_weights_cos]
  have hhalf : (Real.pi : ℂ) / 8 * 4 = (Real.pi : ℂ) / 2 := by ring
  rcases hε with rfl | rfl <;> cases b
  · have htw : turnUnits (false :: w) = 6 := by simpa using ht
    have hpv : p (leftFace (g.1,unusedSlot g false)) = 1 := by
      norm_num [turnUnit] at hf
      omega
    norm_num [htw,hpv,turnUnit,hhalf,Complex.cos_pi_div_two]
  · have htw : turnUnits (true :: w) = 6 := by simpa using ht
    have hpv : p (leftFace (g.1,unusedSlot g true)) = 0 := by
      norm_num [turnUnit] at hf
      omega
    norm_num [htw,hpv,turnUnit,hhalf,Complex.cos_pi_div_two]
  · have htw : turnUnits (false :: w) = -6 := by
      simpa only [neg_one_mul,neg_eq_iff_eq_neg] using ht
    have hpv : p (leftFace (g.1,unusedSlot g false)) = 0 := by
      norm_num [turnUnit] at hf
      omega
    norm_num [htw,hpv,turnUnit,hhalf,Complex.cos_pi_div_two]
  · have htw : turnUnits (true :: w) = -6 := by
      simpa only [neg_one_mul,neg_eq_iff_eq_neg] using ht
    have hpv : p (leftFace (g.1,unusedSlot g true)) = -1 := by
      norm_num [turnUnit] at hf
      omega
    norm_num [htw,hpv,turnUnit,hhalf,Complex.cos_pi_div_two]
end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def stemGerm (g : Germ) (b : Bool) : Germ := (g.1,unusedSlot g b)

def reverseLoopGerm (g : Germ) (b : Bool) : Germ := (g.1,outgoingSlot g b)

@[simp] theorem stem_forward (g : Germ) (b : Bool) :
    advance (stemGerm g b) (!b) = advance g b := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [stemGerm,unusedSlot,advance,outgoingSlot]

@[simp] theorem stem_reverse (g : Germ) (b : Bool) :
    advance (stemGerm g b) b = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [stemGerm,unusedSlot,advance,outgoingSlot,reverseGerm]

@[simp] theorem reverseLoop_advance (g : Germ) (b : Bool) :
    advance (reverseLoopGerm g b) (!b) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,advance,outgoingSlot,reverseGerm]

@[simp] theorem reverseLoop_reverseLoop (g : Germ) (b : Bool) :
    reverseLoopGerm (reverseLoopGerm g b) (!b) = g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,outgoingSlot]

@[simp] theorem reverseLoop_stem (g : Germ) (b : Bool) :
    stemGerm (reverseLoopGerm g b) (!b) = stemGerm g b := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,stemGerm,unusedSlot,outgoingSlot]

@[simp] theorem reverseGerm_advance_eq (g : Germ) (b : Bool) :
    reverseGerm (advance g b) = reverseLoopGerm g b := by
  simp [reverseGerm,advance,reverseLoopGerm]

@[simp] theorem stem_forward_trace (g : Germ) (b : Bool) (w : List Bool) :
    traced (stemGerm g b) ((!b) :: w) = traced g (b :: w) := by
  change g.1 :: traced (advance (stemGerm g b) (!b)) w = _
  rw [stem_forward]
  rfl

@[simp] theorem stem_forward_terminal (g : Germ) (b : Bool) (w : List Bool) :
    terminalGerm (stemGerm g b) ((!b) :: w) = terminalGerm g (b :: w) := by
  simp [terminalGerm]

theorem stem_reverse_trace (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    traced (stemGerm g b) (b :: reverseTurns w) =
      g.1 :: (traced (advance g b) w).reverse := by
  have hr := traced_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  change g.1 :: traced (advance (stemGerm g b) b) (reverseTurns w) = _
  rw [stem_reverse,hr]

theorem reverse_loop_terminal (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    terminalGerm (reverseLoopGerm g b) ((!b) :: reverseTurns w) =
      reverseLoopGerm g b := by
  have hr := terminalGerm_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  simpa only [terminalGerm, reverseLoop_advance, reverseGerm_advance_eq] using hr

theorem reverse_loop_trace (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    traced (reverseLoopGerm g b) ((!b) :: reverseTurns w) =
      g.1 :: (traced (advance g b) w).reverse := by
  have hr := traced_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  change g.1 :: traced (advance (reverseLoopGerm g b) (!b)) (reverseTurns w) = _
  rw [reverseLoop_advance,hr]

theorem reverse_loop_nodup (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) (hN : (traced g (b :: w)).Nodup) :
    (traced (reverseLoopGerm g b) ((!b) :: reverseTurns w)).Nodup := by
  rw [reverse_loop_trace g b w hc]
  simpa [traced] using hN

@[simp] theorem dartFlow_reverse (g : Germ) : dartFlow (reverseGerm g) = -dartFlow g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [dartFlow,edgeOf,dartSign,reverseGerm,neighbor]

@[simp] theorem reverseLoop_outgoing (g : Germ) (b : Bool) :
    ((reverseLoopGerm g b).1,outgoingSlot (reverseLoopGerm g b) (!b)) = g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,outgoingSlot]

theorem wordFlow_reverse (g : Germ) (w : List Bool) :
    wordFlow (reverseGerm (terminalGerm g w)) (reverseTurns w) =
      -wordFlow g w + dartFlow g - dartFlow (terminalGerm g w) := by
  induction w generalizing g with
  | nil => simp [wordFlow,terminalGerm]
  | cons b w ih =>
      simp only [terminalGerm,reverseTurns_cons,wordFlow_append,wordFlow,ih]
      rw [terminalGerm_reverse]
      simp only [reverseGerm_advance_eq,reverseLoop_outgoing,add_zero]
      have hd : dartFlow (advance g b) = -dartFlow (g.1,outgoingSlot g b) := by
        exact dartFlow_reverse (g.1,outgoingSlot g b)
      rw [hd]
      abel

theorem reverse_loop_flow (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    wordFlow (reverseLoopGerm g b) ((!b) :: reverseTurns w) = -wordFlow g (b :: w) := by
  have hr := wordFlow_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  simp only [wordFlow,reverseLoop_outgoing,reverseLoop_advance]
  rw [hr]
  have hd : dartFlow (advance g b) = -dartFlow (g.1,outgoingSlot g b) :=
    dartFlow_reverse (g.1,outgoingSlot g b)
  rw [hd]
  abel

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem neighbor_ne_self (v : Vertex) (k : Fin 3) : neighbor v k ≠ v := by
  cases v <;> fin_cases k <;> simp [neighbor]

@[simp] theorem outgoingSlot_ne (g : Germ) (b : Bool) : outgoingSlot g b ≠ g.2 := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [outgoingSlot]

theorem terminal_previous_mem (g : Germ) (w : List Bool) (hw : w ≠ []) :
    (reverseGerm (terminalGerm g w)).1 ∈ traced g w := by
  induction w generalizing g with
  | nil => contradiction
  | cons b w ih =>
      cases w with
      | nil => simp [terminalGerm,reverseGerm,advance,traced]
      | cons c w =>
          exact List.mem_cons_of_mem _ (ih (advance g b) (by simp))

theorem terminal_previous_suffix (g : Germ) (b : Bool) (w : List Bool) (hw : w ≠ []) :
    (reverseGerm (terminalGerm g (b :: w))).1 ∈ traced (advance g b) w :=
  terminal_previous_mem (advance g b) w hw

theorem return_slot_ne_outgoing (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1) :
    (terminalGerm g (b :: w)).2 ≠ outgoingSlot g b := by
  cases w with
  | nil =>
      have h : neighbor g.1 (outgoingSlot g b) = g.1 := hc
      exact (neighbor_ne_self _ _ h).elim
  | cons c w =>
      intro hs
      cases w with
      | nil =>
          exact outgoingSlot_ne (advance g b) c hs
      | cons d w =>
          have hm := terminal_previous_mem (advance (advance g b) c) (d :: w) (by simp)
          have he : (reverseGerm (terminalGerm (advance (advance g b) c) (d :: w))).1 =
              (advance g b).1 := by
            change neighbor (terminalGerm g (b :: c :: d :: w)).1
              (terminalGerm g (b :: c :: d :: w)).2 = _
            rw [hc,hs]
            rfl
          rw [he] at hm
          exact (List.nodup_cons.mp (List.nodup_cons.mp hN).2).1 hm

theorem return_slot_ne_incoming (g : Germ) (w : List Bool) (hw : w ≠ [])
    (hc : (terminalGerm g w).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (terminalGerm g w).2 ≠ g.2 := by
  intro hs
  have hm := terminal_previous_mem g w hw
  have he : reverseGerm (terminalGerm g w) = reverseGerm g := by
    congr 1
    exact Prod.ext hc hs
  rw [he] at hm
  exact hback hm

theorem collision_root_slots (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w)) :
    stemGerm (terminalGerm g (b :: w)) (!b) = g ∧
    advance (terminalGerm g (b :: w)) (!b) = advance g b := by
  have h1 := return_slot_ne_outgoing g b w hN hc
  have h2 := return_slot_ne_incoming g (b :: w) (by simp) hc hback
  let t := terminalGerm g (b :: w)
  have ht : t.1 = g.1 := hc
  change stemGerm t (!b) = g ∧ advance t (!b) = advance g b
  change t.2 ≠ outgoingSlot g b at h1
  change t.2 ≠ g.2 at h2
  rcases g with ⟨v,k⟩
  rcases t with ⟨v',l⟩
  simp only at ht
  subst v'
  fin_cases k <;> fin_cases l <;> cases b <;>
    simp [outgoingSlot] at h1 h2 ⊢ <;>
    simp [stemGerm,unusedSlot,advance,outgoingSlot]

def reverseAt (g : Germ) (v : Vertex) : List Bool → List Bool
  | [] => []
  | b :: w => if g.1 = v then (!b) :: reverseTurns w
    else b :: reverseAt (advance g b) v w

@[simp] theorem reverseAt_involutive (g : Germ) (v : Vertex) (w : List Bool) :
    reverseAt g v (reverseAt g v w) = w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      by_cases h : g.1 = v
      · simp [reverseAt,h]
      · simp [reverseAt,h,ih]

@[simp] theorem reverseAt_length (g : Germ) (v : Vertex) (w : List Bool) :
    (reverseAt g v w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      by_cases h : g.1 = v <;> simp [reverseAt,h,reverseTurns,ih]

theorem stopped_iff_trace (D : Finset Vertex) (g : Germ) (w : List Bool) :
    Stopped D g w ↔ (traced g w).Nodup ∧ (∀ v ∈ traced g w, v ∈ D) ∧
      ((terminalGerm g w).1 ∉ D ∨ (terminalGerm g w).1 ∈ traced g w) := by
  induction w generalizing D g with
  | nil => simp [Stopped,traced,terminalGerm]
  | cons b w ih =>
      simp only [Stopped,ih,traced,List.nodup_cons,List.mem_cons,terminalGerm]
      constructor
      · rintro ⟨hg,hN,hD,ht⟩
        refine ⟨⟨?_,hN⟩,?_,?_⟩
        · intro hm
          exact (Finset.mem_erase.mp (hD _ hm)).1 rfl
        · intro v hv
          rcases hv with rfl | hv
          · exact hg
          · exact Finset.mem_of_mem_erase (hD _ hv)
        · rcases ht with ht | ht
          · by_cases hm : (terminalGerm (advance g b) w).1 ∈ D
            · right; left
              by_contra hn
              exact ht (Finset.mem_erase.mpr ⟨hn,hm⟩)
            · exact Or.inl hm
          · exact Or.inr (Or.inr ht)
      · rintro ⟨⟨hn,hN⟩,hD,ht⟩
        refine ⟨hD _ (Or.inl rfl),hN,?_,?_⟩
        · intro v hv
          exact Finset.mem_erase.mpr ⟨fun he => hn (he ▸ hv),hD _ (Or.inr hv)⟩
        · rcases ht with ht | ht | ht
          · exact Or.inl (fun h => ht (Finset.mem_of_mem_erase h))
          · exact Or.inl (by simp [ht])
          · exact Or.inr ht

theorem reverse_return_trace (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w)) :
    traced g ((!b) :: reverseTurns w) =
      g.1 :: (traced (advance g b) w).reverse ∧
    (terminalGerm g ((!b) :: reverseTurns w)).1 = g.1 := by
  let t := terminalGerm g (b :: w)
  obtain ⟨hs,ha⟩ := collision_root_slots g b w hN hc hback
  have ht : terminalGerm t ((!b) :: w) = t := by
    change terminalGerm (advance t (!b)) w = t
    rw [ha]
    rfl
  have hr := stem_reverse_trace t (!b) w ht
  have he := reverse_loop_terminal t (!b) w ht
  simp only [Bool.not_not] at hr he
  rw [hs,ha,hc] at hr
  constructor
  · exact hr
  · have hrev : advance g (!b) = advance (reverseLoopGerm t (!b)) b := by
      have h1 := stem_reverse t (!b)
      rw [hs] at h1
      exact h1.trans (by simpa using (reverseLoop_advance t (!b)).symm)
    change (terminalGerm (advance g (!b)) (reverseTurns w)).1 = _
    rw [hrev]
    change (terminalGerm (reverseLoopGerm t (!b)) (b :: reverseTurns w)).1 = _
    rw [he]
    exact hc

@[simp] theorem reverse_advance_vertex (g : Germ) (b : Bool) :
    (reverseGerm (advance g b)).1 = g.1 := by
  simp [reverseGerm, advance]

theorem reverseAt_collision (g : Germ) (v : Vertex) (w : List Bool)
    (hN : (traced g w).Nodup) (hv : v ∈ traced g w)
    (ht : (terminalGerm g w).1 = v)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (traced g (reverseAt g v w)).Perm (traced g w) ∧
    (terminalGerm g (reverseAt g v w)).1 = v := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      by_cases hg : g.1 = v
      · have hc : (terminalGerm g (b :: w)).1 = g.1 := ht.trans hg.symm
        obtain ⟨hr,he⟩ := reverse_return_trace g b w hN hc hback
        simp only [reverseAt,ite_eq_left hg]
        rw [hr]
        exact ⟨List.Perm.cons _ (List.reverse_perm _),he.trans hg⟩
      · have hnt := (List.nodup_cons.mp hN)
        have hvt : v ∈ traced (advance g b) w := by
          simpa only [traced,List.mem_cons,eq_comm (a := v),hg,false_or] using hv
        have hbt : (reverseGerm (advance g b)).1 ∉ traced (advance g b) w := by
          simpa only [reverse_advance_vertex] using hnt.1
        obtain ⟨hp,he⟩ := ih (advance g b) hnt.2 hvt ht hbt
        simp only [reverseAt,ite_eq_right hg,traced,terminalGerm]
        exact ⟨List.Perm.cons _ hp,he⟩

def collisionReverse (g : Germ) (w : List Bool) : List Bool :=
  reverseAt g (terminalGerm g w).1 w

theorem collisionReverse_properties (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (ht : (terminalGerm g w).1 ∈ traced g w)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (traced g (collisionReverse g w)).Perm (traced g w) ∧
    (terminalGerm g (collisionReverse g w)).1 = (terminalGerm g w).1 ∧
    collisionReverse g (collisionReverse g w) = w := by
  obtain ⟨hp,he⟩ := reverseAt_collision g (terminalGerm g w).1 w hN ht rfl hback
  refine ⟨hp,he,?_⟩
  unfold collisionReverse
  rw [he]
  exact reverseAt_involutive _ _ _

theorem collisionReverse_leaf (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : w ∈ leaves D g) (hg : (reverseGerm g).1 ∉ D)
    (ht : (terminalGerm g w).1 ∈ D) :
    collisionReverse g w ∈ leaves D g ∧
    (terminalGerm g (collisionReverse g w)).1 ∈ D ∧
    (∀ v, v ∈ traced g (collisionReverse g w) ↔ v ∈ traced g w) ∧
    collisionReverse g (collisionReverse g w) = w := by
  have hs := (stopped_iff_trace D g w).mp ((mem_leaves_iff D g w).mp hw)
  have hm : (terminalGerm g w).1 ∈ traced g w := hs.2.2.resolve_left (not_not.mpr ht)
  have hb : (reverseGerm g).1 ∉ traced g w := fun h => hg (hs.2.1 _ h)
  obtain ⟨hp,he,hinv⟩ := collisionReverse_properties g w hs.1 hm hb
  refine ⟨(mem_leaves_iff _ _ _).mpr ((stopped_iff_trace _ _ _).mpr ?_),he ▸ ht,
    fun v => hp.mem_iff,hinv⟩
  refine ⟨hp.nodup_iff.mpr hs.1,?_,Or.inr ?_⟩
  · intro v hv
    exact hs.2.1 v (hp.mem_iff.mp hv)
  · rw [he]
    exact hp.mem_iff.mpr hm

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def toRatFinsupp {α : Type*} (p : α →₀ ℤ) : α →₀ ℚ :=
  p.mapRange (fun x : ℤ => (x : ℚ)) (by norm_num)

@[simp] theorem toRatFinsupp_apply {α : Type*} (p : α →₀ ℤ) (a : α) :
    toRatFinsupp p a = (p a : ℚ) := rfl

@[simp] theorem toRatFinsupp_support {α : Type*} (p : α →₀ ℤ) :
    (toRatFinsupp p).support = p.support := by
  ext a
  simp [Finsupp.mem_support_iff]

theorem RepresentsFlow.rational {p : FaceIndex →₀ ℤ} {q : EdgeIndex →₀ ℤ}
    (hp : RepresentsFlow p q) : faceGradient (toRatFinsupp p) = toRatFinsupp q := by
  funext e
  have h := hp (canonicalDart e)
  rcases e with ⟨⟨i,j⟩,k⟩
  simp only [canonicalDart,upEnd,orientedFlow_up] at h
  simp only [faceGradient,toRatFinsupp_apply]
  exact_mod_cast h.symm

theorem cycle_potential_support_subset (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p r : FaceIndex →₀ ℤ) (s : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) (hr : RepresentsFlow r s)
    (hs : s.support ⊆ (wordFlow g w).support) : r.support ⊆ p.support := by
  have hq : ConservedCurrent (toRatFinsupp s) := by
    rw [← hr.rational]
    exact gradient_conserved _
  obtain ⟨c,hc'⟩ := simple_cycle_current_scalar g w hN hc (toRatFinsupp s) hq (by
    intro e he
    have haz : s e = 0 := by
      by_contra hz
      have hm := hs (Finsupp.mem_support_iff.mpr hz)
      exact (Finsupp.mem_support_iff.mp hm) he
    simp [haz])
  have he : toRatFinsupp r = c • toRatFinsupp p := by
    apply finite_gradient_injective
    funext e
    have hz := congrFun hp.rational e
    have hy := congrFun hr.rational e
    change faceGradient (toRatFinsupp r) e = _
    rw [hy,hc' e]
    simp only [faceGradient,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]
    rw [← mul_sub]
    exact congrArg (c * ·) hz.symm
  intro a ha
  rw [Finsupp.mem_support_iff] at ha ⊢
  intro hpz
  have h := congrArg (fun t : FaceIndex →₀ ℚ => t a) he
  simp [hpz] at h
  exact ha h

theorem cycle_potential_support_eq (g h : Germ) (w u : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (hu : (traced h u).Nodup) (hd : terminalGerm h u = h)
    (p r : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (hr : RepresentsFlow r (wordFlow h u))
    (hs : (wordFlow g w).support = (wordFlow h u).support) :
    p.support = r.support := by
  apply Finset.Subset.antisymm
  · exact cycle_potential_support_subset h u hu hd r p (wordFlow g w) hr hp hs.le
  · exact cycle_potential_support_subset g w hw hc p r (wordFlow h u) hp hr hs.ge

def edgeVertices (E : Finset EdgeIndex) : Finset Vertex := E.biUnion fun e => {upEnd e,downEnd e}

@[simp] theorem mem_edgeVertices (E : Finset EdgeIndex) (v : Vertex) :
    v ∈ edgeVertices E ↔ ∃ k : Fin 3, edgeOf (v,k) ∈ E := by
  classical
  constructor
  · intro h
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · refine ⟨e.2,?_⟩
      change edgeOf (canonicalDart e) ∈ E
      simpa using he
    · exact ⟨e.2,by simpa using he⟩
  · rintro ⟨k,hk⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨edgeOf (v,k),hk,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    exact (edgeOf_eq_iff v (edgeOf (v,k))).mp (by simp)

theorem wordContour_has_edge (q : EdgeIndex →₀ ℤ) (g : Germ) (w : List Bool)
    (hw : WordContour q g w) (v : Vertex) (hv : v ∈ traced g w) :
    ∃ k : Fin 3, q (edgeOf (v,k)) ≠ 0 := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      simp only [traced,List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨outgoingSlot g b, fun hz => contour_outgoing_nonzero q g b hw.1
          ((orientedFlow_zero_iff q _).mpr hz)⟩
      · exact ih _ hw.2 hv

theorem wordFlow_edgeVertices (g : Germ) (w : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    edgeVertices (wordFlow g w).support = (traced g w).toFinset := by
  classical
  ext v
  simp only [mem_edgeVertices,Finsupp.mem_support_iff,List.mem_toFinset]
  constructor
  · rintro ⟨k,hk⟩
    by_contra hn
    have h := turnVisit_eq_zero_of_not_mem g w v k hn
    have hz : orientedFlow (wordFlow g w) (v,k) = 0 := by
      rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
      exact h
    exact hk ((orientedFlow_zero_iff _ _).mp hz)
  · exact wordContour_has_edge _ g w (simple_closed_word_contour g w hw hc) v

namespace Polygon

theorem vertices_traversal (P : Polygon) : P.vertices = (traced P.germ P.turns).toFinset := by
  change edgeVertices P.val = _
  rw [← P.traversal.2.2.2]
  exact wordFlow_edgeVertices _ _ P.traversal.2.1 P.traversal.2.2.1

theorem interiorFaces_of_traversal (P : Polygon) (g : Germ) (w : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (hE : (wordFlow g w).support = P.val) (p : FaceIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) : P.interiorFaces = p.support := by
  apply cycle_potential_support_eq P.germ g P.turns w P.traversal.2.1
    P.traversal.2.2.1 hw hc P.potential p P.potential_spec.1 hp
  exact P.traversal.2.2.2.trans hE.symm

@[simp] theorem mem_interior (P : Polygon) (v : Vertex) :
    v ∈ P.interior ↔ v ∈ cellVertices P.interiorFaces ∧ v ∉ P.vertices := by
  simp [interior]

end Polygon


@[simp] theorem mem_inducedEdges (D : Finset Vertex) (e : EdgeIndex) :
    e ∈ inducedEdges D ↔ upEnd e ∈ D ∧ downEnd e ∈ D := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨canonicalDart e,?_,edgeOf_canonical e⟩,h⟩
    exact Finset.mem_product.mpr ⟨h.1,Finset.mem_univ _⟩

@[simp] theorem mem_polygons (D : Finset Vertex) (P : Polygon) :
    P ∈ polygons D ↔ P.vertices ⊆ D := by
  classical
  have hm : P ∈ polygons D ↔ P.val ⊆ inducedEdges D := by
    simp [polygons]
  rw [hm]
  constructor
  · intro h v hv
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hv
    have he' := (mem_inducedEdges D e).mp (h he)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact he'.1
    · exact he'.2
  · intro h e he
    apply (mem_inducedEdges D e).mpr
    constructor
    · exact h (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩)
    · exact h (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩)

noncomputable def vertexLevel (p : FaceIndex →₀ ℤ) (v : Vertex) : ℤ :=
  p (leftFace (v,0))

namespace Polygon

theorem represents (P : Polygon) : RepresentsFlow P.potential (wordFlow P.germ P.turns) :=
  P.potential_spec.1

theorem off_boundary_zero (P : Polygon) (v : Vertex) (hv : v ∉ P.vertices) (k : Fin 3) :
    orientedFlow (wordFlow P.germ P.turns) (v,k) = 0 := by
  apply (orientedFlow_zero_iff _ _).mpr
  by_contra hn
  apply hv
  change v ∈ edgeVertices P.val
  apply (mem_edgeVertices _ _).mpr
  exact ⟨k,by rw [← P.traversal.2.2.2]; exact Finsupp.mem_support_iff.mpr hn⟩

theorem off_boundary_faces (P : Polygon) (v : Vertex) (hv : v ∉ P.vertices) (k : Fin 3) :
    P.potential (leftFace (v,k)) = vertexLevel P.potential v ∧
    P.potential (rightFace (v,k)) = vertexLevel P.potential v := by
  have he (l : Fin 3) : P.potential (leftFace (v,l)) = P.potential (rightFace (v,l)) := by
    have h := P.represents (v,l)
    rw [P.off_boundary_zero v hv l] at h
    omega
  have hl := incident_faces_equal P.potential v he k 0
  exact ⟨hl,(he k).symm.trans hl⟩

theorem interior_iff_level (P : Polygon) (v : Vertex) :
    v ∈ P.interior ↔ v ∉ P.vertices ∧ vertexLevel P.potential v ≠ 0 := by
  rw [P.mem_interior,mem_cellVertices]
  constructor
  · rintro ⟨⟨k,hk⟩,hv⟩
    refine ⟨hv,?_⟩
    change leftFace (v,k) ∈ P.potential.support at hk
    rw [Finsupp.mem_support_iff] at hk
    rwa [(P.off_boundary_faces v hv k).1] at hk
  · rintro ⟨hv,hl⟩
    exact ⟨⟨0,Finsupp.mem_support_iff.mpr hl⟩,hv⟩

theorem step_level (P : Polygon) (v : Vertex) (k : Fin 3)
    (hv : v ∉ P.vertices) (hu : neighbor v k ∉ P.vertices) :
    vertexLevel P.potential (neighbor v k) = vertexLevel P.potential v := by
  rw [← (P.off_boundary_faces (neighbor v k) hu k).1]
  change P.potential (leftFace (reverseGerm (v,k))) = _
  exact (P.off_boundary_faces v hv k).2

theorem interior_exit_on_boundary (P : Polygon) (v : Vertex) (k : Fin 3)
    (hv : v ∈ P.interior) (hu : neighbor v k ∉ P.interior) :
    neighbor v k ∈ P.vertices := by
  by_contra hn
  apply hu
  rw [P.interior_iff_level]
  have h := (P.interior_iff_level v).mp hv
  exact ⟨hn,by rw [P.step_level v k h.1 hn]; exact h.2⟩

theorem trace_level (P : Polygon) (g : Germ) (w : List Bool)
    (hdis : ∀ v ∈ traced g w, v ∉ P.vertices)
    (ht : (terminalGerm g w).1 ∉ P.vertices) :
    vertexLevel P.potential (terminalGerm g w).1 = vertexLevel P.potential g.1 := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      have hg : g.1 ∉ P.vertices := hdis _ (by simp [traced])
      have ha : (advance g b).1 ∉ P.vertices := by
        cases w with
        | nil => exact ht
        | cons c w => exact hdis _ (by simp [traced])
      have htail : ∀ v ∈ traced (advance g b) w, v ∉ P.vertices := by
        intro v hv
        exact hdis v (List.mem_cons_of_mem _ hv)
      exact (ih (advance g b) htail ht).trans (P.step_level g.1 (outgoingSlot g b) hg ha)

theorem trace_left_potential (P : Polygon) (g : Germ) (w : List Bool)
    (hdis : ∀ v ∈ traced g w, v ∉ P.vertices) :
    P.potential (leftFace (terminalGerm g w)) = P.potential (leftFace g) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      have hg : g.1 ∉ P.vertices := hdis _ (by simp [traced])
      have htail : ∀ v ∈ traced (advance g b) w, v ∉ P.vertices := by
        intro v hv
        exact hdis v (List.mem_cons_of_mem _ hv)
      change P.potential (leftFace (terminalGerm (advance g b) w)) = _
      rw [ih (advance g b) htail]
      change P.potential (rightFace (g.1,outgoingSlot g b)) = _
      rw [(P.off_boundary_faces g.1 hg (outgoingSlot g b)).2]
      exact (P.off_boundary_faces g.1 hg g.2).1.symm

theorem outside_level_zero (P : Polygon) (D : Finset Vertex) (hD : Filled D)
    (hP : P ∈ polygons D) (v : Vertex) (hv : v ∉ D) :
    vertexLevel P.potential v = 0 := by
  by_contra hn
  have hb : v ∉ P.vertices := fun h => hv ((mem_polygons D P).mp hP h)
  have hi := (P.interior_iff_level v).mpr ⟨hb,hn⟩
  exact hv (hD P hP hi)

theorem outside_port_potential (P : Polygon) (D : Finset Vertex) (hD : Filled D)
    (hP : P ∈ polygons D) (g : Germ) (hg : (reverseGerm g).1 ∉ D) :
    P.potential (leftFace g) = 0 := by
  have hb : (reverseGerm g).1 ∉ P.vertices :=
    fun h => hg ((mem_polygons D P).mp hP h)
  have he := (P.off_boundary_faces (reverseGerm g).1 hb g.2).2
  have hr : rightFace ((reverseGerm g).1,g.2) = leftFace g := by
    change leftFace (reverseGerm (reverseGerm g)) = _
    rw [reverseGerm_reverseGerm]
  rw [hr] at he
  exact he.trans (P.outside_level_zero D hD hP _ hg)

end Polygon
end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def polygonOfClosed (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) : Polygon :=
  ⟨(wordFlow g w).support,⟨g,w,hne,hN,hc,rfl⟩⟩

theorem polygonOfClosed_vertices (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    (polygonOfClosed g w hne hN hc).vertices = (traced g w).toFinset :=
  wordFlow_edgeVertices g w hN hc

theorem mem_traced_split (g : Germ) (w : List Bool) (v : Vertex) (hv : v ∈ traced g w) :
    ∃ u b t, w = u ++ (b :: t) ∧ (terminalGerm g u).1 = v := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      simp only [traced,List.mem_cons] at hv
      rcases hv with hv | hv
      · exact ⟨[],b,w,rfl,hv.symm⟩
      · obtain ⟨u,c,t,he,ht⟩ := ih (advance g b) hv
        exact ⟨b::u,c,t,by simp [he],ht⟩

theorem reverseAt_append (g : Germ) (v : Vertex) (u w : List Bool)
    (hv : v ∉ traced g u) :
    reverseAt g v (u ++ w) = u ++ reverseAt (terminalGerm g u) v w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih =>
      have hg : g.1 ≠ v := fun h => hv (by simp [traced,h])
      have ht : v ∉ traced (advance g b) u := fun h => hv (List.mem_cons_of_mem _ h)
      simp only [List.cons_append,reverseAt,ite_eq_right hg,terminalGerm,ih _ ht]

theorem split_back_not_mem (g : Germ) (u : List Bool) (b : Bool) (w : List Bool)
    (hN : (traced g (u ++ b :: w)).Nodup)
    (hg : (reverseGerm g).1 ∉ traced g (u ++ b :: w)) :
    (reverseGerm (terminalGerm g u)).1 ∉ traced (terminalGerm g u) (b :: w) := by
  cases u with
  | nil => simpa only [List.nil_append,terminalGerm] using hg
  | cons c u =>
      have hm := terminal_previous_mem g (c :: u) (by simp)
      rw [traced_append] at hN
      have hd := (List.nodup_append.mp hN).2.2
      exact fun ht => hd _ hm _ ht rfl

theorem root_collision_cancels (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w))
    (hz : ∀ (P : Polygon), P.vertices = (traced g (b :: w)).toFinset →
      P.potential (leftFace g) = 0) :
    wordWeight (b :: w) + wordWeight ((!b) :: reverseTurns w) = 0 := by
  let t := terminalGerm g (b :: w)
  obtain ⟨hs,ha⟩ := collision_root_slots g b w hN hc hback
  have htr : traced t ((!b) :: w) = traced g (b :: w) := by
    change t.1 :: traced (advance t (!b)) w = _
    rw [ha,hc]
    rfl
  have hNt : (traced t ((!b) :: w)).Nodup := htr ▸ hN
  have hct : terminalGerm t ((!b) :: w) = t := by
    change terminalGerm (advance t (!b)) w = _
    rw [ha]
    rfl
  let P := polygonOfClosed t ((!b) :: w) (by simp) hNt hct
  have hPv : P.vertices = (traced g (b :: w)).toFinset := by
    rw [polygonOfClosed_vertices,htr]
  have hPz := hz P hPv
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ :=
    simple_closed_word_indicator t ((!b) :: w) (by simp) hNt hct
  have hPs := P.interiorFaces_of_traversal t ((!b) :: w) hNt hct rfl p hp
  have hpz : p (leftFace g) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    rw [← hPs]
    exact Finsupp.notMem_support_iff.mpr hPz
  have hr := collision_phase t (!b) w p ε hNt hct hp hpne hε hvals
  have he : (t.1,unusedSlot t (!b)) = g := hs
  simp only [Bool.not_not,he,hpz,ite_eq_left] at hr
  exact hr

theorem boundary_collision_pair (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D)
    (hw : w ∈ leaves D g) (ht : (terminalGerm g w).1 ∈ D) :
    wordWeight w + wordWeight (collisionReverse g w) = 0 := by
  have hstop := (stopped_iff_trace D g w).mp ((mem_leaves_iff D g w).mp hw)
  have hmem : (terminalGerm g w).1 ∈ traced g w :=
    hstop.2.2.resolve_left (not_not.mpr ht)
  obtain ⟨u,b,t,rfl,hroot⟩ := mem_traced_split g w (terminalGerm g w).1 hmem
  have hN := hstop.1
  rw [traced_append] at hN
  have hna := List.nodup_append.mp hN
  have hb : (reverseGerm (terminalGerm g u)).1 ∉ traced (terminalGerm g u) (b :: t) :=
    split_back_not_mem g u b t hstop.1 (fun h => hg (hstop.2.1 _ h))
  have hct : (terminalGerm (terminalGerm g u) (b :: t)).1 = (terminalGerm g u).1 := by
    rw [← terminalGerm_append]
    exact hroot.symm
  have hzero : wordWeight (b :: t) + wordWeight ((!b) :: reverseTurns t) = 0 := by
    apply root_collision_cancels (terminalGerm g u) b t hna.2.1 hct hb
    intro P hPv
    have hPD : P ∈ polygons D := by
      apply (mem_polygons D P).mpr
      rw [hPv]
      intro v hv
      exact hstop.2.1 v (by rw [traced_append]; exact List.mem_append_right _ (List.mem_toFinset.mp hv))
    have hdis : ∀ v ∈ traced g u, v ∉ P.vertices := by
      intro v hv hm
      rw [hPv,List.mem_toFinset] at hm
      exact hna.2.2 _ hv _ hm rfl
    rw [P.trace_left_potential g u hdis]
    exact P.outside_port_potential D hD hPD g hg
  have hnot : (terminalGerm g (u ++ b :: t)).1 ∉ traced g u := by
    intro hm
    apply hna.2.2 _ hm _ _ rfl
    rw [← hroot]
    simp [traced]
  unfold collisionReverse
  rw [reverseAt_append g _ u (b :: t) hnot]
  have he : (terminalGerm g u).1 = (terminalGerm g (u ++ b :: t)).1 := hroot
  simp only [reverseAt,ite_eq_left he,wordWeight_append]
  rw [← mul_add,hzero,mul_zero]

private theorem collision_subsum_zero (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) (S : Finset (List Bool))
    (hS : ∀ w ∈ S, w ∈ leaves D g ∧ (terminalGerm g w).1 ∈ D)
    (hrev : ∀ w ∈ S, collisionReverse g w ∈ S) :
    (∑ w ∈ S, wordWeight w) = 0 := by
  apply Finset.sum_involution (fun w _ => collisionReverse g w)
  · intro w hw
    exact boundary_collision_pair D g w hD hg (hS w hw).1 (hS w hw).2
  · intro w hw hn he
    apply hn
    have h := boundary_collision_pair D g w hD hg (hS w hw).1 (hS w hw).2
    rw [he] at h
    linear_combination (1 / 2 : ℂ) * h
  · exact hrev
  · intro w hw
    exact (collisionReverse_leaf D g w (hS w hw).1 hg (hS w hw).2).2.2.2

theorem boundary_collision_cancellation (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    collisionSum D g = 0 ∧ ∀ v : Vertex,
      (∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D ∧ v ∈ traced g w
        then wordWeight w else 0) = 0 := by
  classical
  constructor
  · unfold collisionSum
    rw [← Finset.sum_filter]
    apply collision_subsum_zero D g hD hg
    · intro w hw
      exact Finset.mem_filter.mp hw
    · intro w hw
      obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
      have h := collisionReverse_leaf D g w hw hg ht
      exact Finset.mem_filter.mpr ⟨h.1,h.2.1⟩
  · intro v
    rw [← Finset.sum_filter]
    apply collision_subsum_zero D g hD hg
    · intro w hw
      have h := Finset.mem_filter.mp hw
      exact ⟨h.1,h.2.1⟩
    · intro w hw
      obtain ⟨hw,ht,hv⟩ := Finset.mem_filter.mp hw
      have h := collisionReverse_leaf D g w hw hg ht
      exact Finset.mem_filter.mpr ⟨h.1,h.2.1,(h.2.2.1 v).mpr hv⟩
end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem outgoingSlot_injective (g : Germ) : Function.Injective (outgoingSlot g) := by
  intro b c h
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> cases c <;> simp [outgoingSlot] at h ⊢

theorem local_contour_support (q : EdgeIndex →₀ ℤ) (g : Germ) (b : Bool)
    (hq : LocalContour q g b) (k : Fin 3) :
    edgeOf (g.1,k) ∈ q.support ↔ k = g.2 ∨ k = outgoingSlot g b := by
  rw [Finsupp.mem_support_iff]
  change (¬ q (edgeOf (g.1,k)) = 0) ↔ _
  rw [← orientedFlow_zero_iff q (g.1,k),hq k]
  have hn := outgoingSlot_ne g b
  by_cases hi : k = g.2
  · subst k
    simp [Ne.symm hn]
  · by_cases ho : k = outgoingSlot g b
    · subst k
      simp [hn]
    · simp [hi,ho]

theorem local_contour_unique (q r : EdgeIndex →₀ ℤ) (hs : q.support = r.support)
    (g : Germ) (b c : Bool) (hq : LocalContour q g b) (hr : LocalContour r g c) : b = c := by
  apply outgoingSlot_injective g
  have hm : edgeOf (g.1,outgoingSlot g b) ∈ r.support := by
    rw [← hs]
    exact (local_contour_support q g b hq _).mpr (Or.inr rfl)
  have h := (local_contour_support r g c hr _).mp hm
  exact h.resolve_left (outgoingSlot_ne g b)

theorem stopped_contour_unique (D : Finset Vertex) (g : Germ) (w u : List Bool)
    (q r : EdgeIndex →₀ ℤ) (hs : q.support = r.support)
    (hw : Stopped D g w) (hu : Stopped D g u)
    (hqw : WordContour q g w) (hru : WordContour r g u) : w = u := by
  induction w generalizing D g u with
  | nil =>
      cases u with
      | nil => rfl
      | cons c u => exact (hw hu.1).elim
  | cons b w ih =>
      cases u with
      | nil => exact (hu hw.1).elim
      | cons c u =>
          have he := local_contour_unique q r hs g b c hqw.1 hru.1
          subst c
          exact congrArg (List.cons b) (ih (D.erase g.1) (advance g b) u hw.2 hu.2 hqw.2 hru.2)

theorem closed_stopped (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    Stopped (traced g w).toFinset g w := by
  apply (stopped_iff_trace _ _ _).mpr
  refine ⟨hN,by simp,Or.inr ?_⟩
  rw [hc]
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [traced]

theorem closed_traversal_unique (g : Germ) (w u : List Bool)
    (hwne : w ≠ []) (hwN : (traced g w).Nodup) (hwc : terminalGerm g w = g)
    (hune : u ≠ []) (huN : (traced g u).Nodup) (huc : terminalGerm g u = g)
    (hs : (wordFlow g w).support = (wordFlow g u).support) : w = u := by
  have hD : (traced g w).toFinset = (traced g u).toFinset := by
    rw [← wordFlow_edgeVertices g w hwN hwc,← wordFlow_edgeVertices g u huN huc,hs]
  have hu := closed_stopped g u hune huN huc
  rw [← hD] at hu
  exact stopped_contour_unique (traced g w).toFinset g w u _ _ hs
    (closed_stopped g w hwne hwN hwc) hu
    (simple_closed_word_contour g w hwN hwc) (simple_closed_word_contour g u huN huc)

namespace Polygon

def Traverses (P : Polygon) (g : Germ) (w : List Bool) : Prop :=
  w ≠ [] ∧ (traced g w).Nodup ∧ terminalGerm g w = g ∧ (wordFlow g w).support = P.val

theorem traverses_chosen (P : Polygon) : P.Traverses P.germ P.turns := P.traversal

theorem Traverses.vertices {P : Polygon} {g : Germ} {w : List Bool}
    (h : P.Traverses g w) : P.vertices = (traced g w).toFinset := by
  change edgeVertices P.val = _
  rw [← h.2.2.2]
  exact wordFlow_edgeVertices g w h.2.1 h.2.2.1

theorem Traverses.unique {P : Polygon} {g : Germ} {w u : List Bool}
    (h : P.Traverses g w) (h' : P.Traverses g u) : w = u :=
  closed_traversal_unique g w u h.1 h.2.1 h.2.2.1 h'.1 h'.2.1 h'.2.2.1
    (h.2.2.2.trans h'.2.2.2.symm)

theorem Traverses.reverse {P : Polygon} {g : Germ} {b : Bool} {w : List Bool}
    (h : P.Traverses g (b :: w)) :
    P.Traverses (reverseLoopGerm g b) ((!b) :: reverseTurns w) := by
  refine ⟨by simp,reverse_loop_nodup g b w h.2.2.1 h.2.1,
    reverse_loop_terminal g b w h.2.2.1,?_⟩
  rw [reverse_loop_flow g b w h.2.2.1,Finsupp.support_neg,h.2.2.2]

theorem exists_rooted (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    ∃ (k : Fin 3) (w : List Bool), P.Traverses (v,k) w := by
  rw [P.vertices_traversal,List.mem_toFinset] at hv
  obtain ⟨u,b,t,he,hv⟩ := mem_traced_split P.germ P.turns v hv
  have hN : (traced P.germ (u ++ b :: t)).Nodup := he ▸ P.traversal.2.1
  have hc : terminalGerm P.germ (u ++ b :: t) = P.germ := he ▸ P.traversal.2.2.1
  obtain ⟨hN',hc',hq'⟩ := closed_word_rotate P.germ u (b :: t) hN hc
  have hq : (wordFlow (terminalGerm P.germ u) ((b :: t) ++ u)).support = P.val := by
    rw [hq',← he,P.traversal.2.2.2]
  have ht : terminalGerm P.germ u = (v,(terminalGerm P.germ u).2) := Prod.ext hv rfl
  rw [ht] at hN' hc' hq
  exact ⟨(terminalGerm P.germ u).2,(b :: t) ++ u,by simp,hN',hc',hq⟩

end Polygon

def IsCycleAt (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool) : Prop :=
  P.Traverses (v,e.1) e.2

noncomputable def cyclesAt (P : Polygon) (v : Vertex) : Finset (Fin 3 × List Bool) := by
  classical
  exact (Finset.univ.biUnion fun k : Fin 3 =>
    (leaves P.vertices (v,k)).image fun w => (k,w)).filter (IsCycleAt P v)

@[simp] theorem mem_cyclesAt (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool) :
    e ∈ cyclesAt P v ↔ IsCycleAt P v e := by
  classical
  rw [cyclesAt,Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨Finset.mem_biUnion.mpr ⟨e.1,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨e.2,?_,rfl⟩⟩,he⟩
    apply (mem_leaves_iff _ _ _).mpr
    rw [he.vertices]
    exact closed_stopped _ _ he.1 he.2.1 he.2.2.1

def reverseCycle (v : Vertex) (e : Fin 3 × List Bool) : Fin 3 × List Bool :=
  match e.2 with
  | [] => e
  | b :: w => (outgoingSlot (v,e.1) b,(!b) :: reverseTurns w)

theorem cycle_reverse_mem (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool)
    (he : e ∈ cyclesAt P v) : reverseCycle v e ∈ cyclesAt P v := by
  rw [mem_cyclesAt] at he ⊢
  obtain ⟨b,w,hbw⟩ := List.exists_cons_of_ne_nil he.1
  have hr : P.Traverses (v,e.1) (b :: w) := hbw ▸ he
  have hrev := hr.reverse
  simpa only [IsCycleAt,reverseCycle,hbw,reverseLoopGerm] using hrev

theorem cyclesAt_eq_pair (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool)
    (he : e ∈ cyclesAt P v) : cyclesAt P v = {e,reverseCycle v e} := by
  classical
  have htr := (mem_cyclesAt P v e).mp he
  obtain ⟨b,w,hbw⟩ := List.exists_cons_of_ne_nil htr.1
  have hw : P.Traverses (v,e.1) (b :: w) := hbw ▸ htr
  have hr := hw.reverse
  ext f
  constructor
  · intro hf
    have hftr := (mem_cyclesAt P v f).mp hf
    obtain ⟨c,u,hcu⟩ := List.exists_cons_of_ne_nil hftr.1
    have hf' : P.Traverses (v,f.1) (c :: u) := hcu ▸ hftr
    have hm : edgeOf (v,f.1) ∈ (wordFlow (v,e.1) (b :: w)).support := by
      rw [hw.2.2.2,← hf'.2.2.2]
      apply (local_contour_support _ (v,f.1) c
        (simple_closed_word_contour _ _ hf'.2.1 hf'.2.2.1).1 _).mpr
      exact Or.inl rfl
    have hslots := (local_contour_support _ (v,e.1) b
      (simple_closed_word_contour _ _ hw.2.1 hw.2.2.1).1 f.1).mp hm
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases hslots with hs | hs
    · left
      apply Prod.ext hs
      have hst : P.Traverses (v,e.1) f.2 := by
        simpa only [IsCycleAt,hs] using hftr
      exact hst.unique htr
    · right
      have hst : P.Traverses (reverseLoopGerm (v,e.1) b) f.2 := by
        simpa only [IsCycleAt,hs,reverseLoopGerm] using hftr
      have heq := hst.unique hr
      apply Prod.ext
      · simpa only [reverseCycle,hbw] using hs
      · simpa only [reverseCycle,hbw] using heq
  · intro hf
    simp only [Finset.mem_insert,Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact he
    · exact cycle_reverse_mem P v e he

theorem reverseCycle_ne (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool)
    (he : e ∈ cyclesAt P v) : reverseCycle v e ≠ e := by
  obtain ⟨b,w,hbw⟩ := List.exists_cons_of_ne_nil ((mem_cyclesAt P v e).mp he).1
  intro hh
  have hs := congrArg Prod.fst hh
  simp only [reverseCycle,hbw] at hs
  exact outgoingSlot_ne (v,e.1) b hs

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def graphDegree (E : Finset EdgeIndex) (v : Vertex) : ℤ :=
  ∑ k : Fin 3, if edgeOf (v,k) ∈ E then 1 else 0

theorem graphDegree_incidence (E : Finset EdgeIndex) (v : Vertex) :
    graphDegree E v = ∑ e ∈ E,
      ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ) := by
  classical
  have hpair (e : EdgeIndex) : (∑ k : Fin 3, if edgeOf (v,k) = e then (1 : ℤ) else 0) =
      (if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) := by
    rw [Finset.sum_eq_single e.2]
    · simp only [edgeOf_eq_iff]
      by_cases hu : v = upEnd e
      · simp [hu,upEnd_ne_downEnd]
      · by_cases hd : v = downEnd e
        · simp [hd, Ne.symm (upEnd_ne_downEnd e)]
        · simp [hu,hd]
    · intro k _ hk
      have hn : edgeOf (v,k) ≠ e := fun h => hk (by simpa using congrArg Prod.snd h)
      simp [hn]
    · simp
  simp_rw [← hpair]
  rw [Finset.sum_comm]
  unfold graphDegree
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem graphDegree_sum (E : Finset EdgeIndex) :
    ∑ v ∈ edgeVertices E, graphDegree E v = 2 * (E.card : ℤ) := by
  classical
  simp_rw [graphDegree_incidence]
  rw [Finset.sum_comm]
  have he (e : EdgeIndex) (hme : e ∈ E) :
      (∑ v ∈ edgeVertices E,
        ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ)) = 2 := by
    have hu : upEnd e ∈ edgeVertices E := Finset.mem_biUnion.mpr ⟨e,hme,by simp⟩
    have hd : downEnd e ∈ edgeVertices E := Finset.mem_biUnion.mpr ⟨e,hme,by simp⟩
    rw [Finset.sum_add_distrib]
    simp [hu,hd]
  simp_rw [Finset.sum_congr rfl he]
  simp [mul_comm]

namespace Polygon

theorem degree_two (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    graphDegree P.val v = 2 := by
  classical
  obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hw.1
  have hlocal := (simple_closed_word_contour _ _ hw.2.1 hw.2.2.1).1
  unfold graphDegree
  rw [← hw.2.2.2]
  simp_rw [local_contour_support _ (v,k) b hlocal]
  have hne := outgoingSlot_ne (v,k) b
  simp only [Fin.sum_univ_succ]
  fin_cases k <;> cases b <;> norm_num [outgoingSlot] <;> simp

theorem length_eq_card_vertices (P : Polygon) : P.length = P.vertices.card := by
  have h := graphDegree_sum P.val
  change (∑ v ∈ P.vertices, graphDegree P.val v) = _ at h
  have hsum : (∑ v ∈ P.vertices, graphDegree P.val v) = 2 * (P.vertices.card : ℤ) := by
    rw [Finset.sum_congr rfl (fun v hv => P.degree_two v hv)]
    simp [mul_comm]
  rw [hsum] at h
  unfold length
  omega

theorem Traverses.length {P : Polygon} {g : Germ} {w : List Bool}
    (h : P.Traverses g w) : P.length = w.length := by
  rw [P.length_eq_card_vertices,h.vertices,List.toFinset_card_of_nodup h.2.1,traced_length]

theorem length_pos (P : Polygon) : 0 < P.length := by
  rw [P.traverses_chosen.length]
  exact List.length_pos_iff.mpr P.traversal.1

end Polygon


theorem sum_record_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (F : α × β → ℂ) :
    (∑ e ∈ s.biUnion (fun a => (t a).image (fun b => (a,b))), F e) =
      ∑ a ∈ s, ∑ b ∈ t a, F (a,b) := by
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    intro b hb c hc he
    exact (Prod.mk.inj he).2
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
    obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp hf
    exact hab ((Prod.mk.inj (hxe.trans hye.symm)).1)

theorem excursions_fibers (D : Finset Vertex) :
    excursions D = (boundaryGerms D).biUnion fun g =>
      ((leaves D g).filter fun w => (terminalGerm g w).1 ∉ D).image fun w => (g,w) := by
  classical
  ext e
  simp only [mem_excursions,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter]
  constructor
  · intro h
    exact ⟨e.1,(mem_boundaryGerms D e.1).mpr ⟨h.1,h.2.1⟩,e.2,
      ⟨(mem_leaves_iff D e.1 e.2).mpr h.2.2.1,h.2.2.2⟩,rfl⟩
  · rintro ⟨g,hg,w,⟨hw,ht⟩,rfl⟩
    have h := (mem_boundaryGerms D g).mp hg
    exact ⟨h.1,h.2,(mem_leaves_iff _ _ _).mp hw,ht⟩

theorem firstArrivals_fibers (D : Finset Vertex) (v : Vertex) :
    firstArrivals D v = (boundaryGerms D).biUnion fun g =>
      ((leaves (D.erase v) g).filter fun w => (terminalGerm g w).1 = v).image fun w => (g,w) := by
  classical
  ext e
  simp only [mem_firstArrivals,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter]
  constructor
  · intro h
    exact ⟨e.1,h.1,e.2,⟨(mem_leaves_iff _ _ _).mpr h.2.1,h.2.2⟩,rfl⟩
  · rintro ⟨g,hg,w,⟨hw,ht⟩,rfl⟩
    exact ⟨hg,(mem_leaves_iff _ _ _).mp hw,ht⟩

theorem boundary_marked_eq_exits (D : Finset Vertex) (g : Germ) (v : Vertex)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    markedLeaves D g v =
      ∑ w ∈ (leaves D g).filter (fun w => (terminalGerm g w).1 ∉ D),
        if v ∈ traced g w then wordWeight w else 0 := by
  classical
  have hz := (boundary_collision_cancellation D g hD hg).2 v
  unfold markedLeaves
  rw [Finset.sum_filter]
  have he : (∑ w ∈ leaves D g, if v ∈ traced g w then wordWeight w else 0) =
      (∑ w ∈ leaves D g, if (terminalGerm g w).1 ∉ D then
        (if v ∈ traced g w then wordWeight w else 0) else 0) +
      (∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D ∧ v ∈ traced g w
        then wordWeight w else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases ht : (terminalGerm g w).1 ∈ D <;>
      by_cases hv : v ∈ traced g w <;> simp [ht,hv]
  rw [he,hz,add_zero]

theorem visitSum_eq_firstArrivals (D : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hv : v ∈ D) :
    visitSum D v = ∑ e ∈ firstArrivals D v, wordWeight e.2 := by
  classical
  unfold visitSum
  rw [excursions_fibers,firstArrivals_fibers,sum_record_fibers,sum_record_fibers]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← boundary_marked_eq_exits D g v hD ((mem_boundaryGerms _ _).mp hg).2,
    markedLeaves_eq_firstArrival D g v hv]
  simp only [firstArrival,Finset.sum_filter]

theorem rayExits_eq_visitSum (D : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hv : v ∈ D) :
    (∑ e ∈ rayExits D v, wordWeight e.2) = visitSum D v := by
  have h := prefix_ray_reversal D v hv
  rw [← visitSum_eq_firstArrivals D v hD hv] at h
  have hc := congrArg (starRingEnd ℂ) h
  simpa only [visitSum_conj,Complex.conj_conj] using hc.symm
end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

abbrev RayRecord := Fin 3 × List Bool

def rayGerm (v : Vertex) (k : Fin 3) : Germ := (neighbor v k,k)

noncomputable def rayLeaves (D : Finset Vertex) (v : Vertex) : Finset RayRecord :=
  Finset.univ.biUnion fun k : Fin 3 =>
    (leaves (D.erase v) (rayGerm v k)).image fun w => (k,w)

@[simp] theorem mem_rayLeaves (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayLeaves D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 := by
  classical
  simp only [rayLeaves,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,w,hw,he⟩
    subst e
    exact (mem_leaves_iff _ _ _).mp hw
  · intro h
    exact ⟨e.1,e.2,(mem_leaves_iff _ _ _).mpr h,rfl⟩

noncomputable def rayReturns (D : Finset Vertex) (v : Vertex) : Finset RayRecord := by
  classical
  exact (rayLeaves D v).filter fun e => (terminalGerm (rayGerm v e.1) e.2).1 = v

@[simp] theorem mem_rayReturns (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayReturns D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 ∧
      (terminalGerm (rayGerm v e.1) e.2).1 = v := by
  classical
  simp [rayReturns]

def omitRoot (v : Vertex) (e : RayRecord) : RayRecord :=
  match e.2 with
  | [] => e
  | b :: w => (outgoingSlot (v,e.1) b,w)

theorem cycle_omitRoot_mem (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (hP : P ∈ polygons D) (e : RayRecord) (he : e ∈ cyclesAt P v) :
    omitRoot v e ∈ rayReturns D v := by
  have h := (mem_cyclesAt P v e).mp he
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  have htr : P.Traverses (v,e.1) (b :: w) := hw ▸ h
  have hN := List.nodup_cons.mp htr.2.1
  have hd : ∀ u ∈ traced (advance (v,e.1) b) w, u ∈ D.erase v := by
    intro u hu
    refine Finset.mem_erase.mpr ⟨?_,?_⟩
    · intro heq
      subst u
      exact hN.1 hu
    · apply (mem_polygons _ _).mp hP
      rw [htr.vertices]
      simp only [traced,List.mem_toFinset,List.mem_cons]
      exact Or.inr hu
  have hc : (terminalGerm (advance (v,e.1) b) w).1 = v := congrArg Prod.fst htr.2.2.1
  rw [mem_rayReturns]
  simp only [omitRoot,hw]
  change Stopped (D.erase v) (advance (v,e.1) b) w ∧ _
  refine ⟨(stopped_iff_trace _ _ _).mpr ⟨hN.2,hd,Or.inl ?_⟩,hc⟩
  simp [hc]

theorem outgoingSlot_exists (g : Germ) (k : Fin 3) (hk : k ≠ g.2) :
    ∃ b : Bool, outgoingSlot g b = k := by
  rcases g with ⟨v,l⟩
  fin_cases k <;> fin_cases l <;> simp_all [outgoingSlot]

theorem rayReturn_closes (D : Finset Vertex) (v : Vertex) (hv : v ∈ D)
    (e : RayRecord) (he : e ∈ rayReturns D v) :
    ∃ (P : Polygon) (c : RayRecord), P ∈ polygons D ∧ c ∈ cyclesAt P v ∧ omitRoot v c = e := by
  have hs := (mem_rayReturns D v e).mp he
  let g := rayGerm v e.1
  have hne : e.2 ≠ [] := by
    intro hn
    have h := hs.2
    simp only [hn,terminalGerm,rayGerm] at h
    exact neighbor_ne_self _ _ h
  have hstart : g.1 ∈ D.erase v := by
    obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil hne
    exact (show Stopped (D.erase v) g (b :: w) from hw ▸ hs.1).1
  have hexc : IsExcursion (D.erase v) (g,e.2) := by
    refine ⟨hstart,?_,hs.1,?_⟩
    · simp [g,rayGerm,reverseGerm]
    · change (terminalGerm (rayGerm v e.1) e.2).1 ∉ D.erase v
      simp [hs.2]
  let t := terminalGerm g e.2
  have ht : t.1 = v := hs.2
  have hslot : e.1 ≠ t.2 := by
    intro hh
    apply hexc.distinct_ports
    apply Prod.ext
    · change neighbor t.1 t.2 = neighbor v e.1
      rw [ht,hh]
    · exact hh.symm
  obtain ⟨b,hb⟩ := outgoingSlot_exists (v,t.2) e.1 hslot
  have ha : advance (v,t.2) b = g := by
    unfold advance
    rw [hb]
    rfl
  have hfresh := (stopped_iff_trace _ _ _).mp hs.1
  have hN : (traced (v,t.2) (b :: e.2)).Nodup := by
    simp only [traced,ha,List.nodup_cons]
    exact ⟨fun hm => (Finset.mem_erase.mp (hfresh.2.1 v hm)).1 rfl,hfresh.1⟩
  have hc : terminalGerm (v,t.2) (b :: e.2) = (v,t.2) := by
    change terminalGerm (advance (v,t.2) b) e.2 = _
    rw [ha]
    exact Prod.ext ht rfl
  let P := polygonOfClosed (v,t.2) (b :: e.2) (by simp) hN hc
  refine ⟨P,(t.2,b :: e.2),?_,?_,?_⟩
  · apply (mem_polygons D P).mpr
    rw [polygonOfClosed_vertices]
    intro u hu
    simp only [traced,ha,List.mem_toFinset,List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact hv
    · exact Finset.mem_of_mem_erase (hfresh.2.1 u hu)
  · exact (mem_cyclesAt _ _ _).mpr ⟨by simp,hN,hc,rfl⟩
  · simp only [omitRoot,hb]

noncomputable def cyclesIn (D : Finset Vertex) (v : Vertex) : Finset RayRecord :=
  (polygons D).biUnion fun P => cyclesAt P v

theorem cycles_disjoint (v : Vertex) {P Q : Polygon} (hPQ : P ≠ Q) :
    Disjoint (cyclesAt P v) (cyclesAt Q v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  have h := (mem_cyclesAt _ _ _).mp he
  have h' := (mem_cyclesAt _ _ _).mp hf
  exact hPQ (Subtype.ext (h.2.2.2.symm.trans h'.2.2.2))

theorem omitRoot_injOn (D : Finset Vertex) (v : Vertex) :
    Set.InjOn (omitRoot v) (cyclesIn D v) := by
  intro e he f hf hef
  obtain ⟨P,hP,he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨Q,hQ,hf⟩ := Finset.mem_biUnion.mp hf
  have h := (mem_cyclesAt _ _ _).mp he
  have h' := (mem_cyclesAt _ _ _).mp hf
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  obtain ⟨c,u,hu⟩ := List.exists_cons_of_ne_nil h'.1
  have hp := Prod.mk.inj (show (outgoingSlot (v,e.1) b,w) =
      (outgoingSlot (v,f.1) c,u) from by simpa only [omitRoot,hw,hu] using hef)
  have ha : advance (v,e.1) b = advance (v,f.1) c := by simp only [advance,hp.1]
  have ht : (v,e.1) = (v,f.1) := by
    rw [← h.2.2.1,← h'.2.2.1,hw,hu]
    simp only [terminalGerm,ha,hp.2]
  have hes : e.1 = f.1 := congrArg Prod.snd ht
  have heturn : b = c := outgoingSlot_injective (v,f.1) (by simpa only [hes] using hp.1)
  exact Prod.ext hes (by rw [hw,hu,heturn,hp.2])

theorem return_sum_cycles (D : Finset Vertex) (v : Vertex) (hv : v ∈ D) :
    (∑ e ∈ rayReturns D v, wordWeight e.2) =
      ∑ P ∈ polygons D, ∑ e ∈ cyclesAt P v, wordWeight (omitRoot v e).2 := by
  classical
  have hsum : (∑ e ∈ cyclesIn D v, wordWeight (omitRoot v e).2) =
      ∑ e ∈ rayReturns D v, wordWeight e.2 := by
    apply Finset.sum_bij (fun e _ => omitRoot v e)
    · intro e he
      obtain ⟨P,hP,he⟩ := Finset.mem_biUnion.mp he
      exact cycle_omitRoot_mem D v P hP e he
    · intro e he f hf heq
      exact omitRoot_injOn D v he hf heq
    · intro e he
      obtain ⟨P,c,hP,hc,heq⟩ := rayReturn_closes D v hv e he
      exact ⟨c,Finset.mem_biUnion.mpr ⟨P,hP,hc⟩,heq⟩
    · intro e he
      rfl
  rw [← hsum,cyclesIn,Finset.sum_biUnion]
  intro P hP Q hQ hPQ
  exact cycles_disjoint v hPQ



theorem numeric_faceCount_turn (f : Fin 3 → ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hf : ∀ l, f l = 0 ∨ f l = ε)
    (k : Fin 3) (b : Bool)
    (h : ∀ l : Fin 3, f l - f (l+2) =
      (if l = k + (if b then 2 else 1) then 1 else 0) - (if l = k then 1 else 0)) :
    3 - 2 * (∑ l : Fin 3, if f l ≠ 0 then (1 : ℤ) else 0) = ε * turnUnit b := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hf0 := hf 0
  have hf1 := hf 1
  have hf2 := hf 2
  clear h hf
  rcases hε with rfl | rfl <;> fin_cases k <;> cases b <;>
    rcases hf0 with hf0 | hf0 <;> rcases hf1 with hf1 | hf1 <;>
    rcases hf2 with hf2 | hf2 <;>
    simp only [Fin.sum_univ_succ] at * <;> simp_all [turnUnit]

theorem contour_faceCount_turn (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (b : Bool) (hw : LocalContour q g b) :
    3 - 2 * faceCount p.support g.1 = ε * turnUnit b := by
  let f : Fin 3 → ℤ := fun l => p (leftFace (g.1,l))
  have hl (l : Fin 3) : f l - f (l+2) =
      (if l = g.2 + (if b then 2 else 1) then 1 else 0) - (if l = g.2 then 1 else 0) := by
    have h := (hp (g.1,l)).symm.trans (hw l)
    simp only [f,rightFace_prev,outgoingSlot] at h ⊢
    exact h
  simpa only [faceCount,Finsupp.mem_support_iff] using
    numeric_faceCount_turn f ε hε (fun l => hvals _) g.2 b hl

theorem Polygon.ccwTurn_traversal (P : Polygon) (g : Germ) (b : Bool) (w : List Bool)
    (h : P.Traverses g (b :: w)) (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hp : RepresentsFlow p (wordFlow g (b :: w)))
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε) :
    P.ccwTurn g.1 = Real.pi / 3 * (ε * turnUnit b : ℤ) := by
  have ht := contour_faceCount_turn p ε hε hvals _ hp g b
    (simple_closed_word_contour _ _ h.2.1 h.2.2.1).1
  unfold Polygon.ccwTurn
  rw [P.interiorFaces_of_traversal g (b :: w) h.2.1 h.2.2.1 h.2.2.2 p hp]
  congr 1
  exact_mod_cast ht

theorem wordWeight_add_reverse (w : List Bool) :
    wordWeight w + wordWeight (reverseTurns w) =
      (2 : ℂ) * (criticalActivity : ℂ) ^ w.length *
        (Real.cos (Real.pi / 8 * (turnUnits w : ℝ)) : ℂ) := by
  rw [wordWeight_reverse,wordWeight_turnUnits,Complex.exp_ofReal_mul_I]
  simp only [map_mul,map_add,map_pow,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem cycle_return_weight (P : Polygon) (v : Vertex) (e : RayRecord)
    (he : e ∈ cyclesAt P v) :
    wordWeight (omitRoot v e).2 + wordWeight (omitRoot v (reverseCycle v e)).2 =
      (2 : ℂ) * (criticalActivity : ℂ) ^ (P.length - 1) *
        (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ) := by
  have h := (mem_cyclesAt P v e).mp he
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  have htr : P.Traverses (v,e.1) (b :: w) := hw ▸ h
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator (v,e.1) (b :: w)
    (by simp) htr.2.1 htr.2.2.1
  have ht := simple_polygon_signed_turn (v,e.1) (b :: w) (by simp)
    htr.2.1 htr.2.2.1 p ε hp hpne hε hvals
  have hccw := P.ccwTurn_traversal (v,e.1) b w htr p ε hp hε hvals
  simp only [omitRoot,hw,reverseCycle]
  rw [wordWeight_add_reverse]
  have hlen : P.length - 1 = w.length := by rw [htr.length]; simp
  rw [hlen,hccw]
  congr 2
  have htu : turnUnits w = 6 * ε - turnUnit b := by
    rw [turnUnits_cons] at ht
    rcases hε with he | he <;> rw [he] at ht ⊢ <;> nlinarith
  rw [htu]
  push_cast
  rcases hε with rfl | rfl
  · congr 1
    ring
  · norm_num only [Int.cast_neg,Int.cast_one]
    rw [show Real.pi / 8 * ((-6 : ℝ) - (turnUnit b : ℝ)) =
        -((3 / 8 : ℝ) * (2 * Real.pi - Real.pi / 3 * ((-1 : ℝ) * turnUnit b))) by ring]
    exact Real.cos_neg _

theorem cycle_return_sum (P : Polygon) (v : Vertex) :
    (∑ e ∈ cyclesAt P v, wordWeight (omitRoot v e).2) =
      if v ∈ P.vertices then
        (2 : ℂ) * (criticalActivity : ℂ) ^ (P.length - 1) *
          (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ)
      else 0 := by
  classical
  by_cases hv : v ∈ P.vertices
  · obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
    have he := (mem_cyclesAt P v (k,w)).mpr hw
    rw [ite_eq_left hv,cyclesAt_eq_pair P v (k,w) he,Finset.sum_pair
      (Ne.symm (reverseCycle_ne P v (k,w) he))]
    exact cycle_return_weight P v (k,w) he
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro e he
    have h := (mem_cyclesAt P v e).mp he
    obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
    apply False.elim
    apply hv
    rw [h.vertices,hw]
    simp [traced]

theorem return_sum_polygons (D : Finset Vertex) (v : Vertex) (hv : v ∈ D) :
    (∑ e ∈ rayReturns D v, wordWeight e.2) =
      ∑ P ∈ polygons D, if v ∈ P.vertices then
        (2 : ℂ) * (criticalActivity : ℂ) ^ (P.length - 1) *
          (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ)
        else 0 := by
  rw [return_sum_cycles D v hv]
  apply Finset.sum_congr rfl
  intro P hP
  exact cycle_return_sum P v

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor
namespace Polygon

theorem boundary_zero_face (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    ∃ k : Fin 3, P.potential (leftFace (v,k)) = 0 := by
  obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hw.1
  have hloc := (simple_closed_word_contour _ _ hw.2.1 hw.2.2.1).1
  by_contra hn
  push Not at hn
  have hzero (l : Fin 3) : orientedFlow (wordFlow P.germ P.turns) (v,l) = 0 := by
    rw [P.represents (v,l),rightFace_prev]
    have h1 := (P.potential_spec.2.2.2 (leftFace (v,l))).resolve_left (hn l)
    have h2 := (P.potential_spec.2.2.2 (leftFace (v,l+2))).resolve_left (hn (l+2))
    rw [h1,h2,sub_self]
  have hs : edgeOf (v,k) ∈ (wordFlow (v,k) (b :: u)).support :=
    (local_contour_support _ (v,k) b hloc k).mpr (Or.inl rfl)
  rw [hw.2.2.2,← P.traversal.2.2.2,Finsupp.mem_support_iff] at hs
  exact hs ((orientedFlow_zero_iff _ _).mp (hzero k))

theorem interiorFaces_subset (P Q : Polygon) (hQ : Q.vertices ⊆ P.interior) :
    Q.interiorFaces ⊆ P.interiorFaces := by
  have hedge (e : EdgeIndex) (he : e ∈ Q.val) : e ∈ cellEdges P.interiorFaces := by
    have hvQ : upEnd e ∈ Q.vertices := Finset.mem_biUnion.mpr ⟨e,he,by simp⟩
    have hv := (P.interior_iff_level _).mp (hQ hvQ)
    have hl : P.potential (leftFace (canonicalDart e)) ≠ 0 := by
      rw [show canonicalDart e = (upEnd e,e.2) from rfl,
        (P.off_boundary_faces _ hv.1 e.2).1]
      exact hv.2
    exact (mem_cellEdges _ e).mpr (Or.inl (Finsupp.mem_support_iff.mpr hl))
  have h := potential_supported_on_cycle_cells P.germ P.turns
    P.traversal.2.1 P.traversal.2.2.1 P.potential P.represents P.potential_spec.2.1
    (toRatFinsupp Q.potential) (by
      intro e he
      rw [Q.represents.rational,toRatFinsupp_apply]
      have hz : wordFlow Q.germ Q.turns e = 0 := by
        by_contra hn
        exact he (hedge e (by rw [← Q.traversal.2.2.2]; exact Finsupp.mem_support_iff.mpr hn))
      simp [hz])
  simpa only [toRatFinsupp_support,interiorFaces] using h

theorem interior_subset (P Q : Polygon) (hQ : Q.vertices ⊆ P.interior) :
    Q.interior ⊆ P.interior := by
  have hfaces := P.interiorFaces_subset Q hQ
  intro v hv
  have hq := (Q.interior_iff_level v).mp hv
  have hall (k : Fin 3) : P.potential (leftFace (v,k)) ≠ 0 := by
    apply Finsupp.mem_support_iff.mp
    apply hfaces
    apply Finsupp.mem_support_iff.mpr
    rw [(Q.off_boundary_faces v hq.1 k).1]
    exact hq.2
  apply (P.interior_iff_level v).mpr
  constructor
  · intro hb
    obtain ⟨k,hk⟩ := P.boundary_zero_face v hb
    exact hall k hk
  · exact hall 0

theorem interior_filled (P : Polygon) : Filled P.interior := by
  intro Q hQ
  exact P.interior_subset Q ((mem_polygons _ _).mp hQ)

theorem vertices_nonempty (P : Polygon) : P.vertices.Nonempty := by
  rw [P.vertices_traversal]
  obtain ⟨head,tail,hturns⟩ := List.exists_cons_of_ne_nil P.traversal.1
  exact ⟨P.germ.1,by simp [hturns,traced]⟩

theorem interior_card_lt (P : Polygon) (D : Finset Vertex) (hD : Filled D)
    (hP : P ∈ polygons D) : P.interior.card < D.card := by
  obtain ⟨v,hv⟩ := P.vertices_nonempty
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hD P hP,?_⟩
  intro he
  have hvD := (mem_polygons D P).mp hP hv
  rw [← he] at hvD
  exact ((P.mem_interior v).mp hvD).2 hv

end Polygon
end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def stemEnd (v : Vertex) (s : RayRecord) : Germ := terminalGerm (rayGerm v s.1) s.2

def IsPolygonStem (D : Finset Vertex) (v : Vertex) (P : Polygon) (s : RayRecord) : Prop :=
  v ∉ P.vertices ∧ Stopped ((D \ P.vertices).erase v) (rayGerm v s.1) s.2 ∧
    (stemEnd v s).1 ∈ P.vertices

noncomputable def polygonStems (D : Finset Vertex) (v : Vertex) (P : Polygon) :
    Finset RayRecord := by
  classical
  exact (rayLeaves (D \ P.vertices) v).filter (IsPolygonStem D v P)

@[simp] theorem mem_polygonStems (D : Finset Vertex) (v : Vertex) (P : Polygon) (s : RayRecord) :
    s ∈ polygonStems D v P ↔ IsPolygonStem D v P s := by
  classical
  simp only [polygonStems,Finset.mem_filter,mem_rayLeaves]
  exact ⟨And.right,fun h => ⟨h.2.1,h⟩⟩

theorem IsPolygonStem.trace_disjoint {D : Finset Vertex} {v : Vertex} {P : Polygon}
    {s : RayRecord} (hs : IsPolygonStem D v P s) :
    ∀ a ∈ traced (rayGerm v s.1) s.2, a ∉ P.vertices := by
  intro a ha
  exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase
    (((stopped_iff_trace _ _ _).mp hs.2.1).2.1 a ha))).2

theorem IsPolygonStem.back_outside {D : Finset Vertex} {v : Vertex} {P : Polygon}
    {s : RayRecord} (hs : IsPolygonStem D v P s) :
    (reverseGerm (stemEnd v s)).1 ∉ P.vertices := by
  by_cases hn : s.2 = []
  · simpa only [stemEnd,hn,terminalGerm,rayGerm,reverseGerm,neighbor_neighbor] using hs.1
  · exact hs.trace_disjoint _ (terminal_previous_mem _ _ hn)

theorem Polygon.neighbor_mem_of_edge (P : Polygon) (g : Germ)
    (hg : edgeOf g ∈ P.val) : (reverseGerm g).1 ∈ P.vertices := by
  apply (mem_edgeVertices P.val _).mpr
  exact ⟨g.2,by change edgeOf (reverseGerm g) ∈ P.val; simpa using hg⟩

theorem thirdSlot_unique (g : Germ) (b : Bool) (k : Fin 3)
    (hi : k ≠ g.2) (ho : k ≠ outgoingSlot g b) : k = unusedSlot g b := by
  rcases g with ⟨v,l⟩
  fin_cases k <;> fin_cases l <;> cases b <;>
    simp [outgoingSlot,unusedSlot] at hi ho ⊢

theorem stemGerm_eq_of_back_outside (P : Polygon) (t : Germ) (k : Fin 3)
    (b : Bool) (w : List Bool) (hc : P.Traverses (t.1,k) (b :: w))
    (hb : (reverseGerm t).1 ∉ P.vertices) : stemGerm (t.1,k) b = t := by
  have hn : edgeOf t ∉ P.val := fun h => hb (P.neighbor_mem_of_edge t h)
  have hloc := (simple_closed_word_contour _ _ hc.2.1 hc.2.2.1).1
  have hslots : ¬ (t.2 = k ∨ t.2 = outgoingSlot (t.1,k) b) := by
    intro hh
    apply hn
    rw [← hc.2.2.2]
    exact (local_contour_support _ (t.1,k) b hloc t.2).mpr hh
  have h := thirdSlot_unique (t.1,k) b t.2
    (fun he => hslots (Or.inl he)) (fun he => hslots (Or.inr he))
  exact Prod.ext rfl h.symm

def attachWord (c : RayRecord) : List Bool :=
  match c.2 with
  | [] => []
  | b :: w => (!b) :: w

theorem attachWord_injective_on_words (c d : RayRecord) (h : attachWord c = attachWord d) :
    c.2 = d.2 := by
  cases hc : c.2 with
  | nil => cases hd : d.2 <;> simp_all [attachWord]
  | cons b w =>
      cases hd : d.2 with
      | nil => simp_all [attachWord]
      | cons e u =>
          have hp : (!b) = (!e) ∧ w = u := by simpa only [attachWord,hc,hd,List.cons.injEq] using h
          have hbe : b = e := by simpa using congrArg Bool.not hp.1
          simp only [hbe,hp.2]

theorem attached_trace (P : Polygon) (t : Germ) (c : RayRecord)
    (hc : c ∈ cyclesAt P t.1) (hb : (reverseGerm t).1 ∉ P.vertices) :
    traced t (attachWord c) = traced (t.1,c.1) c.2 ∧
    terminalGerm t (attachWord c) = (t.1,c.1) := by
  have h := (mem_cyclesAt P t.1 c).mp hc
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  have htr : P.Traverses (t.1,c.1) (b :: w) := hw ▸ h
  have he := stemGerm_eq_of_back_outside P t c.1 b w htr hb
  simp only [attachWord,hw]
  constructor
  · rw [← he,stem_forward_trace]
    rfl
  · rw [← he,stem_forward_terminal]
    exact htr.2.2.1

theorem first_cut_unique (g : Germ) (a : Vertex) (u r u' r' : List Bool)
    (he : u ++ r = u' ++ r')
    (hu : (terminalGerm g u).1 = a) (hu' : (terminalGerm g u').1 = a)
    (hn : a ∉ traced g u) (hn' : a ∉ traced g u') : u = u' := by
  induction u generalizing g u' with
  | nil =>
      cases u' with
      | nil => rfl
      | cons b u' => exact (hn' (by simp [traced,← hu,terminalGerm])).elim
  | cons b u ih =>
      cases u' with
      | nil => exact (hn (by simp [traced,← hu',terminalGerm])).elim
      | cons c u' =>
          simp only [List.cons_append,List.cons.injEq] at he
          rcases he with ⟨rfl,he⟩
          apply congrArg (List.cons b)
          exact ih (advance g b) u' he hu hu'
            (fun h => hn (List.mem_cons_of_mem _ h))
            (fun h => hn' (List.mem_cons_of_mem _ h))

def spliceRecord (v : Vertex) (s c : RayRecord) : RayRecord :=
  ((rayGerm v s.1).2,s.2 ++ attachWord c)

noncomputable def rayCollisions (D : Finset Vertex) (v : Vertex) : Finset RayRecord := by
  classical
  exact (rayLeaves D v).filter fun e => (stemEnd v e).1 ∈ D.erase v

@[simp] theorem mem_rayCollisions (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayCollisions D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 ∧
      (stemEnd v e).1 ∈ D.erase v := by
  classical
  simp [rayCollisions]

theorem spliceRecord_mem (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (hP : P ∈ polygons D) (s : RayRecord) (hs : s ∈ polygonStems D v P)
    (c : RayRecord) (hc : c ∈ cyclesAt P (stemEnd v s).1) :
    spliceRecord v s c ∈ rayCollisions D v := by
  have hs := (mem_polygonStems D v P s).mp hs
  have htr := (mem_cyclesAt P _ c).mp hc
  have hat := attached_trace P (stemEnd v s) c hc hs.back_outside
  have hN := (stopped_iff_trace _ _ _).mp hs.2.1
  have hct : (stemEnd v (spliceRecord v s c)).1 = (stemEnd v s).1 := by
    simp only [stemEnd,spliceRecord,terminalGerm_append]
    have hh := congrArg (fun g : Germ => g.1) hat.2
    exact hh
  have htmem : (stemEnd v s).1 ∈ D.erase v :=
    Finset.mem_erase.mpr ⟨fun h => hs.1 (h ▸ hs.2.2),(mem_polygons D P).mp hP hs.2.2⟩
  rw [mem_rayCollisions]
  refine ⟨?_,by rw [hct]; exact htmem⟩
  apply (stopped_iff_trace _ _ _).mpr
  have htrace : traced (rayGerm v (spliceRecord v s c).1) (spliceRecord v s c).2 =
      traced (rayGerm v s.1) s.2 ++ traced ((stemEnd v s).1,c.1) c.2 := by
    change traced (rayGerm v s.1) (s.2 ++ attachWord c) = _
    rw [traced_append]
    change traced (rayGerm v s.1) s.2 ++ traced (stemEnd v s) (attachWord c) = _
    rw [hat.1]
  rw [htrace]
  refine ⟨List.nodup_append.mpr ⟨hN.1,htr.2.1,?_⟩,?_,Or.inr ?_⟩
  · intro a ha b hb hab
    subst b
    exact hs.trace_disjoint a ha (by rw [htr.vertices]; exact List.mem_toFinset.mpr hb)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hN.2.1 a ha)).1,
        (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase (hN.2.1 a ha))).1⟩
    · have haP : a ∈ P.vertices := by rw [htr.vertices]; exact List.mem_toFinset.mpr ha
      exact Finset.mem_erase.mpr ⟨fun h => hs.1 (h ▸ haP),(mem_polygons D P).mp hP haP⟩
  · change (stemEnd v (spliceRecord v s c)).1 ∈ _
    rw [hct]
    apply List.mem_append_right
    obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil htr.1
    simp [hw,traced]

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem sum_record_three {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (t : α → Finset β) (u : α → β → Finset γ) (F : α × β × γ → ℂ) :
    (∑ z ∈ s.biUnion (fun a => ((t a).biUnion (fun b =>
      (u a b).image (fun c => (b,c)))).image (fun bc => (a,bc))), F z) =
      ∑ a ∈ s, ∑ b ∈ t a, ∑ c ∈ u a b, F (a,b,c) := by
  have h := sum_record_fibers s (fun a => (t a).biUnion (fun b =>
    (u a b).image (fun c => (b,c)))) F
  apply h.trans
  apply Finset.sum_congr rfl
  intro a ha
  exact sum_record_fibers (t a) (u a) (fun bc => F (a,bc))



theorem collision_splice_surjective (D : Finset Vertex) (v : Vertex)
    (e : RayRecord) (he : e ∈ rayCollisions D v) :
    ∃ (P : Polygon) (s c : RayRecord), P ∈ polygons D ∧ s ∈ polygonStems D v P ∧
      c ∈ cyclesAt P (stemEnd v s).1 ∧ spliceRecord v s c = e := by
  classical
  rcases e with ⟨k,w⟩
  have hs := (mem_rayCollisions D v (k,w)).mp he
  let g := rayGerm v k
  have hn := (stopped_iff_trace _ _ _).mp hs.1
  have hm : (terminalGerm g w).1 ∈ traced g w :=
    hn.2.2.resolve_left (not_not.mpr hs.2)
  obtain ⟨u,b,r,hw,hroot⟩ := mem_traced_split g w (terminalGerm g w).1 hm
  have hN : (traced g (u ++ b :: r)).Nodup := hw ▸ hn.1
  have hd : ∀ a ∈ traced g (u ++ b :: r), a ∈ D.erase v := hw ▸ hn.2.1
  have hna := List.nodup_append.mp (show (traced g u ++ traced (terminalGerm g u) (b :: r)).Nodup by
    rwa [← traced_append])
  let f := terminalGerm g u
  have hf : (terminalGerm f (b :: r)).1 = f.1 := by
    change (terminalGerm (terminalGerm g u) (b :: r)).1 = _
    rw [← terminalGerm_append,← hw]
    exact hroot.symm
  have hback : (reverseGerm f).1 ∉ traced f (b :: r) := by
    apply split_back_not_mem g u b r hN
    intro hm
    have hv := (Finset.mem_erase.mp (hd _ hm)).1
    apply hv
    simp [g,rayGerm,reverseGerm]
  obtain ⟨hslot,ha⟩ := collision_root_slots f b r hna.2.1 hf hback
  let t := terminalGerm f (b :: r)
  have ht : t.1 = f.1 := hf
  have htr : traced t ((!b) :: r) = traced f (b :: r) := by
    change t.1 :: traced (advance t (!b)) r = _
    rw [ha,ht]
    rfl
  have hNt : (traced t ((!b) :: r)).Nodup := htr ▸ hna.2.1
  have hct : terminalGerm t ((!b) :: r) = t := by
    change terminalGerm (advance t (!b)) r = _
    rw [ha]
    rfl
  let P := polygonOfClosed t ((!b) :: r) (by simp) hNt hct
  have hPv : P.vertices = (traced f (b :: r)).toFinset := by
    rw [polygonOfClosed_vertices,htr]
  have hPD : P ∈ polygons D := by
    apply (mem_polygons D P).mpr
    rw [hPv]
    intro a ha
    exact Finset.mem_of_mem_erase (hd a (by rw [traced_append]; exact List.mem_append_right _ (List.mem_toFinset.mp ha)))
  have hnv : v ∉ P.vertices := by
    rw [hPv]
    intro hv
    exact (Finset.mem_erase.mp (hd v (by rw [traced_append]; exact List.mem_append_right _ (List.mem_toFinset.mp hv)))).1 rfl
  have hsf : (k,u) ∈ polygonStems D v P := by
    rw [mem_polygonStems]
    refine ⟨hnv,(stopped_iff_trace _ _ _).mpr ⟨hna.1,?_,Or.inl ?_⟩,?_⟩
    · intro a ha
      have hDa := hd a (by rw [traced_append]; exact List.mem_append_left _ ha)
      refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hDa).1,Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hDa,?_⟩⟩
      rw [hPv]
      intro hPa
      exact hna.2.2 a ha a (List.mem_toFinset.mp hPa) rfl
    · intro ha
      have hnot := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase ha)).2
      apply hnot
      rw [hPv]
      simp only [List.mem_toFinset,traced,List.mem_cons]
      exact Or.inl rfl
    · change f.1 ∈ P.vertices
      rw [hPv]
      simp [traced]
  have het : (f.1,t.2) = t := Prod.ext ht.symm rfl
  refine ⟨P,(k,u),(t.2,(!b) :: r),hPD,hsf,?_,?_⟩
  · rw [mem_cyclesAt]
    change P.Traverses (f.1,t.2) ((!b) :: r)
    rw [het]
    exact ⟨by simp,hNt,hct,rfl⟩
  · simp only [spliceRecord,attachWord,Bool.not_not]
    exact Prod.ext rfl hw.symm

theorem spliceRecord_terminal {D : Finset Vertex} (v : Vertex) (P : Polygon) (s c : RayRecord)
    (hs : IsPolygonStem D v P s) (hc : c ∈ cyclesAt P (stemEnd v s).1) :
    stemEnd v (spliceRecord v s c) = ((stemEnd v s).1,c.1) := by
  change terminalGerm (rayGerm v s.1) (s.2 ++ attachWord c) = _
  rw [terminalGerm_append]
  exact (attached_trace P (stemEnd v s) c hc hs.back_outside).2

theorem collision_splice_injective (D : Finset Vertex) (v : Vertex)
    (P Q : Polygon) (s t c d : RayRecord)
    (hs : s ∈ polygonStems D v P) (ht : t ∈ polygonStems D v Q)
    (hc : c ∈ cyclesAt P (stemEnd v s).1) (hd : d ∈ cyclesAt Q (stemEnd v t).1)
    (he : spliceRecord v s c = spliceRecord v t d) : P = Q ∧ s = t ∧ c = d := by
  have hs' := (mem_polygonStems D v P s).mp hs
  have ht' := (mem_polygonStems D v Q t).mp ht
  have hends := congrArg (stemEnd v) he
  rw [spliceRecord_terminal v P s c hs' hc,spliceRecord_terminal v Q t d ht' hd] at hends
  have hends := Prod.mk.inj hends
  have hwords : s.1 = t.1 ∧
      s.2 ++ attachWord c = t.2 ++ attachWord d := Prod.mk.inj he
  have hst : s.2 = t.2 := by
    apply first_cut_unique (rayGerm v s.1) (stemEnd v s).1 s.2 (attachWord c) t.2 (attachWord d) hwords.2 rfl
    · rw [hwords.1]
      exact hends.1.symm
    · exact fun h => hs'.trace_disjoint _ h hs'.2.2
    · rw [hwords.1]
      exact fun h => ht'.trace_disjoint _ h (hends.1.symm ▸ ht'.2.2)
  have hst' : s = t := Prod.ext hwords.1 hst
  subst t
  have hcdw := attachWord_injective_on_words c d (List.append_cancel_left hwords.2)
  have hcd : c = d := Prod.ext hends.2 hcdw
  subst d
  have hp := (mem_cyclesAt _ _ _).mp hc
  have hq := (mem_cyclesAt _ _ _).mp hd
  exact ⟨Subtype.ext (hp.2.2.2.symm.trans hq.2.2.2),rfl,rfl⟩

noncomputable def collisionData (D : Finset Vertex) (v : Vertex) : Finset (Polygon × RayRecord × RayRecord) := by
  classical
  exact (polygons D).biUnion fun P =>
    ((polygonStems D v P).biUnion fun s =>
      (cyclesAt P (stemEnd v s).1).image fun c => (s,c)).image fun sc => (P,sc)

@[simp] theorem mem_collisionData (D : Finset Vertex) (v : Vertex) (P : Polygon) (s c : RayRecord) :
    (P,s,c) ∈ collisionData D v ↔ P ∈ polygons D ∧ s ∈ polygonStems D v P ∧
      c ∈ cyclesAt P (stemEnd v s).1 := by
  classical
  simp only [collisionData,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨Q,hQ,⟨t,d⟩,⟨z,hz,a,ha,hza⟩,hQz⟩
    have he := Prod.mk.inj hQz
    have he' := Prod.mk.inj hza
    rcases he with ⟨rfl,he⟩
    have hzs : z = s := he'.1.trans (congrArg Prod.fst he)
    have hac : a = c := he'.2.trans (congrArg Prod.snd he)
    subst z
    subst a
    exact ⟨hQ,hz,ha⟩
  · rintro ⟨hP,hs,hc⟩
    exact ⟨P,hP,(s,c),⟨s,hs,c,hc,rfl⟩,rfl⟩

theorem collisionData_sum (D : Finset Vertex) (v : Vertex) :
    (∑ z ∈ collisionData D v, wordWeight (spliceRecord v z.2.1 z.2.2).2) =
      ∑ P ∈ polygons D, ∑ s ∈ polygonStems D v P,
        ∑ c ∈ cyclesAt P (stemEnd v s).1, wordWeight (spliceRecord v s c).2 := by
  classical
  unfold collisionData
  convert sum_record_three (polygons D) (polygonStems D v)
    (fun P s => cyclesAt P (stemEnd v s).1)
    (fun z : Polygon × RayRecord × RayRecord => wordWeight (spliceRecord v z.2.1 z.2.2).2) using 1
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_image]

theorem collision_sum_grouped (D : Finset Vertex) (v : Vertex) :
    (∑ e ∈ rayCollisions D v, wordWeight e.2) =
      ∑ P ∈ polygons D, ∑ s ∈ polygonStems D v P,
        ∑ c ∈ cyclesAt P (stemEnd v s).1, wordWeight (spliceRecord v s c).2 := by
  classical
  have hsum : (∑ z ∈ collisionData D v, wordWeight (spliceRecord v z.2.1 z.2.2).2) =
      ∑ e ∈ rayCollisions D v, wordWeight e.2 := by
    apply Finset.sum_bij (fun z _ => spliceRecord v z.2.1 z.2.2)
    · intro z hz
      have h := (mem_collisionData D v z.1 z.2.1 z.2.2).mp hz
      exact spliceRecord_mem D v z.1 h.1 z.2.1 h.2.1 z.2.2 h.2.2
    · intro z hz y hy he
      have h := (mem_collisionData D v z.1 z.2.1 z.2.2).mp hz
      have h' := (mem_collisionData D v y.1 y.2.1 y.2.2).mp hy
      have heq := collision_splice_injective D v z.1 y.1 z.2.1 y.2.1 z.2.2 y.2.2 h.2.1 h'.2.1 h.2.2 h'.2.2 he
      exact Prod.ext heq.1 (Prod.ext heq.2.1 heq.2.2)
    · intro e he
      obtain ⟨P,s,c,hP,hs,hc,rfl⟩ := collision_splice_surjective D v e he
      exact ⟨(P,s,c),(mem_collisionData D v P s c).mpr ⟨hP,hs,hc⟩,rfl⟩
    · intro z hz
      rfl
  exact hsum.symm.trans (collisionData_sum D v)

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem IsPolygonStem.left_potential {D : Finset Vertex} {v : Vertex} {P : Polygon}
    {s : RayRecord} (hs : IsPolygonStem D v P s) :
    P.potential (leftFace (stemEnd v s)) = vertexLevel P.potential v := by
  rw [stemEnd,P.trace_left_potential _ _ hs.trace_disjoint]
  change P.potential (rightFace (v,s.1)) = _
  exact (P.off_boundary_faces v hs.1 s.1).2

theorem collision_cycle_weight (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (s c : RayRecord) (hs : s ∈ polygonStems D v P)
    (hc : c ∈ cyclesAt P (stemEnd v s).1) :
    wordWeight (attachWord c) + wordWeight (attachWord (reverseCycle (stemEnd v s).1 c)) =
      if v ∈ P.interior then -2 * (criticalActivity : ℂ) ^ P.length else 0 := by
  classical
  have hs' := (mem_polygonStems D v P s).mp hs
  have h := (mem_cyclesAt P _ c).mp hc
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  let g : Germ := ((stemEnd v s).1,c.1)
  have htr : P.Traverses g (b :: w) := hw ▸ h
  have he := stemGerm_eq_of_back_outside P (stemEnd v s) c.1 b w htr hs'.back_outside
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g (b :: w)
    (by simp) htr.2.1 htr.2.2.1
  have hfaces := P.interiorFaces_of_traversal g (b :: w) htr.2.1 htr.2.2.1 htr.2.2.2 p hp
  have hz : p (leftFace (stemEnd v s)) = 0 ↔ v ∉ P.interior := by
    rw [P.interior_iff_level]
    simp only [hs'.1,not_false_eq_true,true_and,not_not]
    rw [← hs'.left_potential]
    constructor
    · intro h
      apply Finsupp.notMem_support_iff.mp
      change leftFace (stemEnd v s) ∉ P.interiorFaces
      rw [hfaces]
      exact Finsupp.notMem_support_iff.mpr h
    · intro h
      apply Finsupp.notMem_support_iff.mp
      rw [← hfaces]
      exact Finsupp.notMem_support_iff.mpr h

  have hphase := collision_phase g b w p ε htr.2.1 htr.2.2.1 hp hpne hε hvals
  change stemGerm g b = stemEnd v s at he
  change wordWeight ((!b) :: w) + wordWeight (b :: reverseTurns w) =
    if p (leftFace (stemGerm g b)) = 0 then 0 else _ at hphase
  rw [he,← htr.length] at hphase
  simp only [attachWord,hw,reverseCycle,Bool.not_not]
  rw [hphase]
  by_cases hv : v ∈ P.interior
  · rw [ite_eq_left hv,ite_eq_right (fun h => hz.mp h hv)]
  · rw [ite_eq_right hv,ite_eq_left (hz.mpr hv)]

theorem collision_cycle_sum (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (s : RayRecord) (hs : s ∈ polygonStems D v P) :
    (∑ c ∈ cyclesAt P (stemEnd v s).1, wordWeight (spliceRecord v s c).2) =
      if v ∈ P.interior then -2 * (criticalActivity : ℂ) ^ P.length * wordWeight s.2 else 0 := by
  classical
  have hs' := (mem_polygonStems D v P s).mp hs
  obtain ⟨k,w,hw⟩ := P.exists_rooted (stemEnd v s).1 hs'.2.2
  have he := (mem_cyclesAt P _ (k,w)).mpr hw
  rw [cyclesAt_eq_pair P _ (k,w) he,Finset.sum_pair (Ne.symm (reverseCycle_ne P _ (k,w) he))]
  simp only [spliceRecord,wordWeight_append]
  rw [← mul_add,collision_cycle_weight D v P s (k,w) hs he]
  split_ifs <;> ring

theorem Polygon.trace_interior_of_back (P : Polygon) (g : Germ) (w : List Bool)
    (hb : (reverseGerm g).1 ∈ P.interior)
    (hd : ∀ a ∈ traced g w, a ∉ P.vertices) :
    (∀ a ∈ traced g w, a ∈ P.interior) ∧ (reverseGerm (terminalGerm g w)).1 ∈ P.interior := by
  induction w generalizing g with
  | nil => exact ⟨by simp [traced],hb⟩
  | cons b w ih =>
      have hg : g.1 ∈ P.interior := by
        by_contra hn
        have he := P.interior_exit_on_boundary (reverseGerm g).1 g.2 hb
          (by simpa [reverseGerm] using hn)
        apply hd g.1 (by simp [traced])
        simpa [reverseGerm] using he
      have ha : (reverseGerm (advance g b)).1 ∈ P.interior := by
        simpa [advance,reverseGerm] using hg
      have hi := ih (advance g b) ha (fun a hm => hd a (List.mem_cons_of_mem _ hm))
      refine ⟨?_,hi.2⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hg
      · exact hi.1 a ha

theorem polygonStems_eq_rayExits (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (hD : Filled D) (hP : P ∈ polygons D) (hv : v ∈ P.interior) :
    polygonStems D v P = rayExits P.interior v := by
  classical
  ext s
  rw [mem_polygonStems,mem_rayExits]
  have hb : (reverseGerm (rayGerm v s.1)).1 ∈ P.interior := by simpa [rayGerm,reverseGerm] using hv
  constructor
  · intro hs
    have hn := (stopped_iff_trace _ _ _).mp hs.2.1
    have hi := P.trace_interior_of_back (rayGerm v s.1) s.2 hb hs.trace_disjoint
    have ht : (stemEnd v s).1 ∉ P.interior := fun h => ((P.mem_interior _).mp h).2 hs.2.2
    refine ⟨(stopped_iff_trace _ _ _).mpr ⟨hn.1,?_,Or.inl ?_⟩,ht⟩
    · intro a ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hn.2.1 a ha)).1,hi.1 a ha⟩
    · exact fun h => ht (Finset.mem_of_mem_erase h)
  · rintro ⟨hs,he⟩
    have hn := (stopped_iff_trace _ _ _).mp hs
    have hd : ∀ a ∈ traced (rayGerm v s.1) s.2, a ∉ P.vertices := by
      intro a ha
      exact ((P.mem_interior a).mp (Finset.mem_of_mem_erase (hn.2.1 a ha))).2
    have hi := P.trace_interior_of_back (rayGerm v s.1) s.2 hb hd
    have ht : (stemEnd v s).1 ∈ P.vertices := by
      have h := P.interior_exit_on_boundary (reverseGerm (stemEnd v s)).1 (stemEnd v s).2 hi.2
        (by simpa only [reverseGerm,neighbor_neighbor,stemEnd,rayGerm] using he)
      simpa [reverseGerm] using h
    refine ⟨((P.mem_interior v).mp hv).2,(stopped_iff_trace _ _ _).mpr ⟨hn.1,?_,Or.inl ?_⟩,ht⟩
    · intro a ha
      have hpa := hn.2.1 a ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hpa).1,
        Finset.mem_sdiff.mpr ⟨hD P hP (Finset.mem_of_mem_erase hpa),hd a ha⟩⟩
    · exact fun h => (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).2 ht

theorem collision_sum_polygons (D : Finset Vertex) (v : Vertex) (hD : Filled D) :
    (∑ e ∈ rayCollisions D v, wordWeight e.2) =
      ∑ P ∈ polygons D, if v ∈ P.interior then
        -2 * (criticalActivity : ℂ) ^ P.length * visitSum P.interior v else 0 := by
  classical
  rw [collision_sum_grouped]
  apply Finset.sum_congr rfl
  intro P hP
  have hsum : (∑ s ∈ polygonStems D v P, ∑ c ∈ cyclesAt P (stemEnd v s).1,
          wordWeight (spliceRecord v s c).2) =
      ∑ s ∈ polygonStems D v P, if v ∈ P.interior then
        -2 * (criticalActivity : ℂ) ^ P.length * wordWeight s.2 else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    exact collision_cycle_sum D v P s hs
  rw [hsum]
  by_cases hv : v ∈ P.interior
  · simp only [ite_eq_left hv]
    rw [← Finset.mul_sum,polygonStems_eq_rayExits D v P hD hP hv,
      rayExits_eq_visitSum P.interior v P.interior_filled hv]
  · simp [hv]

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def boxIndex : Vertex → Fin 3 → ℤ
  | .up i j, k => if k = 0 then j else if k = 1 then i else i+j
  | .down i j, k => if k = 0 then j else if k = 1 then i else i+j+1

def BoxMem (lo hi : Fin 3 → ℤ) (v : Vertex) : Prop :=
  ∀ k, lo k ≤ boxIndex v k ∧ boxIndex v k < hi k

theorem tilingCoordinate_index (v : Vertex) (k : Fin 3) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      tilingCoordinate k (position v) = (boxIndex v k : ℝ) + a := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  cases v with
  | up i j =>
    fin_cases k
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
  | down i j =>
    fin_cases k
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring

theorem integer_bounds_fraction (lo hi n : ℤ) (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    ((lo : ℝ) < (n : ℝ)+a ∧ (n : ℝ)+a < (hi : ℝ)) ↔ lo ≤ n ∧ n < hi := by
  constructor
  · rintro ⟨hl,hh⟩
    constructor
    · by_contra h
      have h' : n+1 ≤ lo := by omega
      have : (n : ℝ)+1 ≤ (lo : ℝ) := by exact_mod_cast h'
      linarith
    · by_contra h
      have h' : hi ≤ n := by omega
      have : (hi : ℝ) ≤ (n : ℝ) := by exact_mod_cast h'
      linarith
  · rintro ⟨hl,hh⟩
    have hl' : (lo : ℝ) ≤ (n : ℝ) := by exact_mod_cast hl
    have hh' : (n : ℝ)+1 ≤ (hi : ℝ) := by exact_mod_cast (show n+1 ≤ hi by omega)
    constructor <;> linarith

theorem admissiblyConvex_box (D : Finset Vertex) (hD : AdmissiblyConvex D) :
    ∃ lo hi : Fin 3 → ℤ, ∀ v, v ∈ D ↔ BoxMem lo hi v := by
  obtain ⟨lo,hi,h⟩ := hD
  refine ⟨lo,hi,fun v => ?_⟩
  rw [h]
  apply forall_congr'
  intro k
  obtain ⟨a,ha,ha',he⟩ := tilingCoordinate_index v k
  rw [he]
  exact integer_bounds_fraction _ _ _ _ ha ha'

def starFaces (D : Finset Vertex) : Finset FaceIndex :=
  D.biUnion fun v => Finset.univ.image fun k : Fin 3 => leftFace (v,k)

theorem mem_starFaces (D : Finset Vertex) (a : FaceIndex) :
    a ∈ starFaces D ↔ ∃ v ∈ faceVertices a, v ∈ D := by
  simp only [starFaces,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    mem_faceVertices]
  aesop

theorem incident_mem_starFaces {D : Finset Vertex} {v : Vertex} (hv : v ∈ D)
    (k : Fin 3) : leftFace (v,k) ∈ starFaces D := by
  apply (mem_starFaces D _).mpr
  exact ⟨v,(mem_faceVertices _ _).mpr ⟨k,rfl⟩,hv⟩



theorem boxMem_iff_three (lo hi : Fin 3 → ℤ) (v : Vertex) : BoxMem lo hi v ↔
    (lo 0 ≤ boxIndex v 0 ∧ boxIndex v 0 < hi 0) ∧ (lo 1 ≤ boxIndex v 1 ∧ boxIndex v 1 < hi 1) ∧
      (lo 2 ≤ boxIndex v 2 ∧ boxIndex v 2 < hi 2) := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ k
    fin_cases k
    exacts [h0, h1, h2]

theorem boxIndex_up_zero (i j : ℤ) : boxIndex (.up i j) 0 = j := rfl
theorem boxIndex_up_one (i j : ℤ) : boxIndex (.up i j) 1 = i := rfl
theorem boxIndex_up_two (i j : ℤ) : boxIndex (.up i j) 2 = i + j := rfl
theorem boxIndex_down_zero (i j : ℤ) : boxIndex (.down i j) 0 = j := rfl
theorem boxIndex_down_one (i j : ℤ) : boxIndex (.down i j) 1 = i := rfl
theorem boxIndex_down_two (i j : ℤ) : boxIndex (.down i j) 2 = i + j + 1 := rfl

theorem box_opposite_face (lo hi : Fin 3 → ℤ) (v r : Vertex) (k : Fin 3)
    (hv : BoxMem lo hi (neighbor v k))
    (hr : r ∈ faceVertices (leftFace (v,k+1)))
    (hr' : BoxMem lo hi r) : BoxMem lo hi v := by
  cases v <;> fin_cases k <;>
    simp only [leftFace,Fin.reduceAdd,Fin.zero_eta,Fin.isValue,Fin.reduceEq,ite_true,
      ite_false,faceVertices,Finset.mem_insert,Finset.mem_singleton] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [neighbor,Fin.reduceAdd,Fin.zero_eta,Fin.isValue,Fin.mk_one,Fin.reduceFinMk,Fin.reduceEq,↓reduceIte,
      boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hv hr' ⊢ <;> omega

theorem outside_opposite_face (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) (k : Fin 3) (hv : v ∉ D) (hn : neighbor v k ∈ D) :
    leftFace (v,k+1) ∉ starFaces D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  intro hf
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp hf
  exact hv ((hbox v).mpr (box_opposite_face lo hi v r k ((hbox _).mp hn) hr
    ((hbox _).mp hr')))

theorem box_two_faces_up0 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,0)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((0 : Fin 3)+1),(0 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((0 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  simp only [neighbor,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,↓reduceIte,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hr' hs' <;> omega

theorem box_two_faces_up1 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,1)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((1 : Fin 3)+1),(1 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((1 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  simp only [neighbor,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,↓reduceIte,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hr' hs' <;> omega

theorem box_two_faces_up2 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,2)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((2 : Fin 3)+1),(2 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((2 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  simp only [neighbor,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,↓reduceIte,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hr' hs' <;> omega

theorem box_two_faces_down0 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,0)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((0 : Fin 3)+1),(0 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((0 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  simp only [neighbor,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,↓reduceIte,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hr' hs' <;> omega

theorem box_two_faces_down1 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,1)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((1 : Fin 3)+1),(1 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((1 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  simp only [neighbor,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,↓reduceIte,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hr' hs' <;> omega

theorem box_two_faces_down2 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,2)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((2 : Fin 3)+1),(2 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((2 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  simp only [neighbor,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,↓reduceIte,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hr' hs' <;> omega

theorem box_two_faces (lo hi : Fin 3 → ℤ) (v r s : Vertex) (k : Fin 3)
    (hr : r ∈ faceVertices (rightFace (v,k)))
    (hs : s ∈ faceVertices (leftFace (neighbor v (k+1),k+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi v ∨ BoxMem lo hi (neighbor v (k+1)) := by
  cases v with
  | up i j =>
    fin_cases k
    · exact box_two_faces_up0 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_up1 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_up2 lo hi i j r s hr hs hr' hs'
  | down i j =>
    fin_cases k
    · exact box_two_faces_down0 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_down1 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_down2 lo hi i j r s hr hs hr' hs'

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def OnFaceBoundary (S : Finset FaceIndex) (g : Germ) : Prop :=
  leftFace g ∉ S ∧ rightFace g ∈ S

noncomputable def faceBoundaryTurn (S : Finset FaceIndex) (g : Germ) : Bool :=
  decide (leftFace (g.1,g.2+1) ∉ S)

theorem faceBoundary_advance (S : Finset FaceIndex) (g : Germ)
    (hg : OnFaceBoundary S g) :
    OnFaceBoundary S (advance g (faceBoundaryTurn S g)) := by
  classical
  rcases g with ⟨v,k⟩
  have h := hg
  simp only [OnFaceBoundary,rightFace_prev] at h
  unfold faceBoundaryTurn
  by_cases ht : leftFace (v,k+1) ∈ S
  · simp only [ht,not_true_eq_false,decide_false]
    cases v <;> fin_cases k <;>
      simp_all [OnFaceBoundary,advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor]
  · simp only [ht,not_false_eq_true,decide_true]
    cases v <;> fin_cases k <;>
      simp_all [OnFaceBoundary,advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor]

theorem faceBoundary_germ_unique (S : Finset FaceIndex) (v : Vertex) (k l : Fin 3)
    (hk : OnFaceBoundary S (v,k)) (hl : OnFaceBoundary S (v,l)) : k = l := by
  simp only [OnFaceBoundary,rightFace_prev] at hk hl
  fin_cases k <;> fin_cases l <;> norm_num at hk hl ⊢ <;> tauto

theorem faceBoundary_vertex_mem (S : Finset FaceIndex) (g : Germ)
    (hg : OnFaceBoundary S g) : g.1 ∈ cellVertices S := by
  apply (mem_cellVertices _ _).mpr
  exact ⟨g.2+2,by simpa only [rightFace_prev] using
    (show rightFace (g.1,g.2) ∈ S from hg.2)⟩

abbrev FaceBoundary (S : Finset FaceIndex) := {g : Germ // OnFaceBoundary S g}

noncomputable instance faceBoundaryFinite (S : Finset FaceIndex) : Finite (FaceBoundary S) := by
  let f : FaceBoundary S → (cellVertices S) × Fin 3 :=
    fun g => (⟨g.val.1,faceBoundary_vertex_mem S g.val g.property⟩,g.val.2)
  apply Finite.of_injective f
  intro g h he
  apply Subtype.ext
  have hv := congrArg (fun x : (cellVertices S) × Fin 3 => (x.1.val,x.2)) he
  exact hv

noncomputable def faceBoundaryNext (S : Finset FaceIndex) (g : FaceBoundary S) : FaceBoundary S :=
  ⟨advance g.val (faceBoundaryTurn S g.val),faceBoundary_advance S _ g.property⟩

theorem faceBoundary_vertex_injective (S : Finset FaceIndex) :
    Function.Injective (fun g : FaceBoundary S => g.val.1) := by
  intro ⟨⟨v,k⟩,hk⟩ ⟨⟨u,l⟩,hl⟩ he
  dsimp at he
  subst u
  have := faceBoundary_germ_unique S v k l hk hl
  subst l
  rfl

theorem faceBoundaryNext_injective (S : Finset FaceIndex) :
    Function.Injective (faceBoundaryNext S) := by
  intro g h he
  apply faceBoundary_vertex_injective S
  have hval := congrArg Subtype.val he
  have hv := congrArg (fun d : Germ => neighbor d.1 d.2) hval
  simpa only [faceBoundaryNext,advance,neighbor_neighbor] using hv

noncomputable def faceBoundaryWord (S : Finset FaceIndex) (g : FaceBoundary S) : ℕ → List Bool
  | 0 => []
  | n+1 => faceBoundaryTurn S g.val :: faceBoundaryWord S (faceBoundaryNext S g) n

theorem faceBoundaryWord_length (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    (faceBoundaryWord S g n).length = n := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => simp [faceBoundaryWord,ih]

theorem faceBoundaryWord_terminal (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    terminalGerm g.val (faceBoundaryWord S g n) = ((faceBoundaryNext S)^[n] g).val := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [faceBoundaryWord,terminalGerm,Function.iterate_succ_apply]
    exact ih (faceBoundaryNext S g)

theorem faceBoundaryWord_traced (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    traced g.val (faceBoundaryWord S g n) =
      List.ofFn (fun i : Fin n => ((faceBoundaryNext S)^[i.val] g).val.1) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,traced]
  | succ n ih =>
    simp only [faceBoundaryWord,traced,List.ofFn_succ,Fin.val_zero,Function.iterate_zero,
      id_eq,Fin.val_succ,Function.iterate_succ_apply]
    congr 1
    exact ih (faceBoundaryNext S g)

theorem faceBoundary_closed_word (S : Finset FaceIndex) (g : FaceBoundary S) :
    ∃ n : ℕ, 0 < n ∧ (traced g.val (faceBoundaryWord S g n)).Nodup ∧
      terminalGerm g.val (faceBoundaryWord S g n) = g.val := by
  let n := Function.minimalPeriod (faceBoundaryNext S) g
  refine ⟨n,Function.minimalPeriod_pos_of_mem_periodicPts
    ((faceBoundaryNext_injective S).mem_periodicPts g),?_,?_⟩
  · rw [faceBoundaryWord_traced,List.nodup_ofFn]
    intro i j he
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt
    exact faceBoundary_vertex_injective S he
  · rw [faceBoundaryWord_terminal,Function.iterate_minimalPeriod]

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem faceBoundaryTurn_false (S : Finset FaceIndex) (g : Germ) :
    faceBoundaryTurn S g = false ↔ leftFace (g.1,g.2+1) ∈ S := by
  classical
  simp [faceBoundaryTurn]

theorem star_boundary_outside (D : Finset Vertex) (g : FaceBoundary (starFaces D)) :
    g.val.1 ∉ D := by
  intro hv
  exact g.property.1 (incident_mem_starFaces hv g.val.2)

theorem outside_boundary_germ (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) (k : Fin 3) (hv : v ∉ D) (hn : neighbor v k ∈ D) :
    OnFaceBoundary (starFaces D) (v,k+1) ∧
      faceBoundaryTurn (starFaces D) (v,k+1) = false := by
  have hR : rightFace (v,k) ∈ starFaces D := incident_mem_starFaces hn k
  have hL : leftFace (v,k) ∈ starFaces D := by
    have h := incident_mem_starFaces hn (k+2)
    simpa only [← rightFace_prev,rightFace,reverseGerm,neighbor_neighbor] using h
  have hO := outside_opposite_face D hD v k hv hn
  constructor
  · refine ⟨hO,?_⟩
    rw [rightFace_prev]
    convert hL using 1
    congr 2
    fin_cases k <;> decide
  · rw [faceBoundaryTurn_false]
    simpa only [rightFace_prev,add_assoc,Fin.reduceAdd] using hR

theorem star_boundary_no_double_negative (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (hg : faceBoundaryTurn (starFaces D) g.val = false) :
    faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val = true := by
  classical
  by_contra hn
  have hn' : faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val =
      false := by
    cases he : (faceBoundaryTurn (starFaces D)
      (faceBoundaryNext (starFaces D) g).val) <;> simp_all
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp g.property.2
  have hs_mem := (faceBoundaryTurn_false _ _).mp hn'
  have hs_mem' : leftFace (neighbor g.val.1 (g.val.2+1),g.val.2+2) ∈ starFaces D := by
    simpa [faceBoundaryNext,hg,advance,outgoingSlot,add_assoc] using hs_mem
  obtain ⟨s,hs,hs'⟩ := (mem_starFaces D _).mp hs_mem'
  rcases box_two_faces lo hi g.val.1 r s g.val.2 hr hs ((hbox _).mp hr')
    ((hbox _).mp hs') with h | h
  · exact star_boundary_outside D g ((hbox _).mpr h)
  · apply star_boundary_outside D (faceBoundaryNext (starFaces D) g)
    simpa only [faceBoundaryNext,advance,hg,outgoingSlot,Bool.false_eq_true,ite_false]
      using (hbox _).mpr h

noncomputable def boundaryCharge (S : Finset FaceIndex) (g : FaceBoundary S) : ℤ :=
  if faceBoundaryTurn S g.val then 0 else 1

theorem star_boundary_turn_charge (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) :
    boundaryCharge (starFaces D) (faceBoundaryNext (starFaces D) g) -
      boundaryCharge (starFaces D) g ≤ turnUnit (faceBoundaryTurn (starFaces D) g.val) := by
  cases hg : faceBoundaryTurn (starFaces D) g.val
  · have hn := star_boundary_no_double_negative D hD g hg
    simp [boundaryCharge,hg,hn,turnUnit]
  · cases hn : faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val <;>
      simp [boundaryCharge,hg,hn,turnUnit]

theorem star_boundary_word_charge (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) :
    boundaryCharge (starFaces D) ((faceBoundaryNext (starFaces D))^[n] g) -
      boundaryCharge (starFaces D) g ≤ turnUnits (faceBoundaryWord (starFaces D) g n) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,turnUnits]
  | succ n ih =>
    have h₁ := star_boundary_turn_charge D hD g
    have h₂ := ih (faceBoundaryNext (starFaces D) g)
    simp only [faceBoundaryWord,turnUnits,List.map_cons,List.sum_cons,
      Function.iterate_succ_apply] at *
    omega

theorem star_boundary_cycle_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) (hn : 0 < n)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val) :
    turnUnits (faceBoundaryWord (starFaces D) g n) = 6 := by
  have hne : faceBoundaryWord (starFaces D) g n ≠ [] := by
    intro he
    have hl := faceBoundaryWord_length (starFaces D) g n
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have h := star_boundary_word_charge D hD g n
  have he : ((faceBoundaryNext (starFaces D))^[n] g) = g := by
    apply Subtype.ext
    rwa [faceBoundaryWord_terminal] at hc
  rw [he,sub_self] at h
  rcases simple_polygon_turning g.val _ hne hN hc with h' | h' <;> omega

theorem box_face_row_interval_0 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up i₁ j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  simp only [faceVertices,Finset.exists_mem_insert,Finset.mem_singleton,exists_eq_left,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two] at hr' ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hs' <;> omega

theorem box_face_row_interval_1 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down i₁ (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  simp only [faceVertices,Finset.exists_mem_insert,Finset.mem_singleton,exists_eq_left,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two] at hr' ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hs' <;> omega

theorem box_face_row_interval_2 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up (i₁+1) (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  simp only [faceVertices,Finset.exists_mem_insert,Finset.mem_singleton,exists_eq_left,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two] at hr' ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hs' <;> omega

theorem box_face_row_interval_3 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down i₁ j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  simp only [faceVertices,Finset.exists_mem_insert,Finset.mem_singleton,exists_eq_left,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two] at hr' ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hs' <;> omega

theorem box_face_row_interval_4 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up (i₁+1) j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  simp only [faceVertices,Finset.exists_mem_insert,Finset.mem_singleton,exists_eq_left,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two] at hr' ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hs' <;> omega

theorem box_face_row_interval_5 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down (i₁+1) (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  simp only [faceVertices,Finset.exists_mem_insert,Finset.mem_singleton,exists_eq_left,
    boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
    boxIndex_down_one,boxIndex_down_two] at hr' ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boxMem_iff_three,boxIndex_up_zero,boxIndex_up_one,boxIndex_up_two,boxIndex_down_zero,
      boxIndex_down_one,boxIndex_down_two] at hs' <;> omega

theorem box_face_row_interval (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (r s : Vertex)
    (hr : r ∈ faceVertices (i₁,j)) (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact box_face_row_interval_0 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_1 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_2 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_3 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_4 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_5 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'

theorem star_face_row_interval (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (i₁ i i₂ j : ℤ) (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂)
    (hf₁ : (i₁,j) ∈ starFaces D) (hf₂ : (i₂,j) ∈ starFaces D) :
    (i,j) ∈ starFaces D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp hf₁
  obtain ⟨s,hs,hs'⟩ := (mem_starFaces D _).mp hf₂
  obtain ⟨v,hv,hv'⟩ := box_face_row_interval lo hi i₁ i i₂ j h₁ h₂ r s hr hs
    ((hbox _).mp hr') ((hbox _).mp hs')
  exact (mem_starFaces D _).mpr ⟨v,hv,(hbox _).mpr hv'⟩

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def faceIndicator (S : Finset FaceIndex) (a : FaceIndex) : ℤ := if a ∈ S then 1 else 0

theorem faceBoundary_local (S : Finset FaceIndex) (g : FaceBoundary S) (k : Fin 3) :
    faceIndicator S (leftFace (g.val.1,k)) - faceIndicator S (rightFace (g.val.1,k)) =
    (if k = outgoingSlot g.val (faceBoundaryTurn S g.val) then 1 else 0) -
      (if k = g.val.2 then 1 else 0) := by
  classical
  rcases g with ⟨⟨v,l⟩,h⟩
  simp only [OnFaceBoundary,rightFace_prev] at h
  by_cases ht : leftFace (v,l+1) ∈ S
  · simp only [faceBoundaryTurn,ht,not_true_eq_false,decide_false]
    fin_cases l <;> fin_cases k <;>
      simp_all [faceIndicator,rightFace_prev,outgoingSlot]
  · simp only [faceBoundaryTurn,ht,not_false_eq_true,decide_true]
    fin_cases l <;> fin_cases k <;>
      simp_all [faceIndicator,rightFace_prev,outgoingSlot]

theorem faceBoundaryWord_local (S : Finset FaceIndex) (g : FaceBoundary S)
    (n : ℕ) (q : EdgeIndex →₀ ℤ)
    (hq : WordContour q g.val (faceBoundaryWord S g n)) :
    ∀ v ∈ traced g.val (faceBoundaryWord S g n), ∀ k : Fin 3,
      orientedFlow q (v,k) = faceIndicator S (leftFace (v,k)) -
        faceIndicator S (rightFace (v,k)) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,traced]
  | succ n ih =>
    intro v hv k
    simp only [faceBoundaryWord,traced,List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (hq.1 k).trans (faceBoundary_local S g k).symm
    · exact ih (faceBoundaryNext S g) hq.2 v hv k

theorem faceBoundaryWord_gradient (S : Finset FaceIndex) (g : FaceBoundary S)
    (n : ℕ) (hN : (traced g.val (faceBoundaryWord S g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord S g n) = g.val)
    (e : EdgeIndex) (he : wordFlow g.val (faceBoundaryWord S g n) e ≠ 0) :
    wordFlow g.val (faceBoundaryWord S g n) e =
      faceIndicator S (leftFace (canonicalDart e)) -
        faceIndicator S (rightFace (canonicalDart e)) := by
  have hv : upEnd e ∈ traced g.val (faceBoundaryWord S g n) := by
    have hm : upEnd e ∈ edgeVertices (wordFlow g.val (faceBoundaryWord S g n)).support := by
      apply Finset.mem_biUnion.mpr
      exact ⟨e,Finsupp.mem_support_iff.mpr he,by simp⟩
    rwa [wordFlow_edgeVertices _ _ hN hc,List.mem_toFinset] at hm
  have h := faceBoundaryWord_local S g n _ (simple_closed_word_contour _ _ hN hc)
    _ hv e.2
  rcases e with ⟨⟨i,j⟩,k⟩
  simpa only [upEnd,canonicalDart,orientedFlow_up] using h

theorem finite_indicator_row_containment (p : FaceIndex →₀ ℤ) (S : Finset FaceIndex)
    (hval : ∀ a, p a = 0 ∨ p a = 1)
    (hgrad : ∀ i j : ℤ, p (i,j) ≠ p (i-1,j) →
      p (i,j) - p (i-1,j) = faceIndicator S (i,j) - faceIndicator S (i-1,j))
    (hrow : ∀ i₁ i i₂ j : ℤ, i₁ ≤ i → i ≤ i₂ → (i₁,j) ∈ S → (i₂,j) ∈ S →
      (i,j) ∈ S) : p.support ⊆ S := by
  classical
  rintro ⟨i,j⟩ ha
  let R := (p.support.filter fun a => a.2 = j).image Prod.fst
  have hRmem (x : ℤ) : x ∈ R ↔ p (x,j) ≠ 0 := by
    simp only [R,Finset.mem_image,Finset.mem_filter,Finsupp.mem_support_iff]
    constructor
    · rintro ⟨⟨u,v⟩,⟨hp,hj⟩,hi⟩
      dsimp at hj hi
      subst v; subst u
      exact hp
    · intro hx
      exact ⟨(x,j),⟨hx,rfl⟩,rfl⟩
  have hi : i ∈ R := (hRmem i).mpr (Finsupp.mem_support_iff.mp ha)
  have hne : R.Nonempty := ⟨i,hi⟩
  let a := R.min' hne
  let b := R.max' hne
  have haR : a ∈ R := R.min'_mem hne
  have hbR : b ∈ R := R.max'_mem hne
  have hpa : p (a,j) = 1 := (hval _).resolve_left ((hRmem a).mp haR)
  have hpb : p (b,j) = 1 := (hval _).resolve_left ((hRmem b).mp hbR)
  have hpa' : p (a-1,j) = 0 := by
    by_contra hz
    have hm := R.min'_le (a-1) ((hRmem _).mpr hz)
    change a ≤ a-1 at hm
    omega
  have hpb' : p (b+1,j) = 0 := by
    by_contra hz
    have hm := R.le_max' (b+1) ((hRmem _).mpr hz)
    change b+1 ≤ b at hm
    omega
  have haS : (a,j) ∈ S := by
    have h := hgrad a j (by omega)
    rw [hpa,hpa'] at h
    by_contra hn
    simp only [faceIndicator,ite_eq_right hn] at h
    split_ifs at h <;> omega
  have hbS : (b,j) ∈ S := by
    have he : b+1-1 = b := by omega
    have h := hgrad (b+1) j (by rw [he,hpb,hpb']; norm_num)
    rw [he,hpb,hpb'] at h
    by_contra hn
    simp only [faceIndicator,ite_eq_right hn] at h
    split_ifs at h <;> omega
  exact hrow a i b j (R.min'_le _ hi) (R.le_max' _ hi) haS hbS

theorem star_boundary_potential_contained (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p
      (wordFlow g.val (faceBoundaryWord (starFaces D) g n)))
    (hval : ∀ a, p a = 0 ∨ p a = 1) : p.support ⊆ starFaces D := by
  apply finite_indicator_row_containment p (starFaces D) hval
  · intro i j he
    have h : wordFlow g.val (faceBoundaryWord (starFaces D) g n) ((i,j),0) ≠ 0 := by
      rw [hp.horizontal]
      exact sub_ne_zero.mpr he
    have he' := faceBoundaryWord_gradient (starFaces D) g n hN hc ((i,j),0) h
    rw [hp.horizontal] at he'
    simpa [canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] using he'
  · exact star_face_row_interval D hD



theorem contour_unused_advance (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (hl : LocalContour q g false) :
    p (leftFace (advance g true)) = p (leftFace (g.1,unusedSlot g false)) := by
  have h := (hp (g.1,unusedSlot g false)).symm.trans (hl (unusedSlot g false))
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [advance,outgoingSlot,unusedSlot,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

theorem star_boundary_trace_outside (D : Finset Vertex)
    (g : FaceBoundary (starFaces D)) (n : ℕ) :
    ∀ v ∈ traced g.val (faceBoundaryWord (starFaces D) g n), v ∉ D := by
  intro v hv
  rw [faceBoundaryWord_traced,List.mem_ofFn] at hv
  obtain ⟨i,rfl⟩ := hv
  exact star_boundary_outside D _

theorem star_boundary_endpoint (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) (hn : 0 < n)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (hg : faceBoundaryTurn (starFaces D) g.val = false)
    (e : Germ) (w : List Bool) (he : e = advance g.val true)
    (hd : ∀ v ∈ traced e w, v ∈ D)
    (hu : (terminalGerm e w).1 ∉ D)
    (hu' : (reverseGerm (terminalGerm e w)).1 ∈ D) :
    (terminalGerm e w).1 ∈ traced g.val (faceBoundaryWord (starFaces D) g n) := by
  classical
  let W := faceBoundaryWord (starFaces D) g n
  have hne : W ≠ [] := by
    intro hx
    have hl := faceBoundaryWord_length (starFaces D) g n
    change W.length = n at hl
    rw [hx] at hl
    simp only [List.length_nil] at hl
    omega
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g.val W hne hN hc
  have ht := simple_polygon_signed_turn g.val W hne hN hc p ε hp hpne hε hvals
  have ht' := star_boundary_cycle_turn D hD g n hn hN hc
  have heps : ε = 1 := by change turnUnits W = 6 at ht'; rw [ht'] at ht; omega
  subst ε
  have hpS := star_boundary_potential_contained D hD g n hN hc p hp hvals
  let P : Polygon := ⟨(wordFlow g.val W).support,⟨g.val,W,hne,hN,hc,rfl⟩⟩
  have hPv : P.vertices = (traced g.val W).toFinset :=
    wordFlow_edgeVertices g.val W hN hc
  have hPf : P.interiorFaces = p.support :=
    P.interiorFaces_of_traversal g.val W hN hc rfl p hp
  have hdis : ∀ v ∈ traced e w, v ∉ P.vertices := by
    intro v hv hm
    rw [hPv,List.mem_toFinset] at hm
    exact star_boundary_trace_outside D g n v hm (hd v hv)
  have hlocal : LocalContour (wordFlow g.val W) g.val false := by
    have hh := simple_closed_word_contour g.val W hN hc
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa only [W,faceBoundaryWord,hg,WordContour] using hh.1
  have hused := contour_unused_face p 1 (Or.inl rfl) hvals _ hp g.val false hlocal
  have hpone : p (leftFace e) = 1 := by
    rw [he,contour_unused_advance p _ hp g.val hlocal]
    norm_num [turnUnit] at hused
    omega
  have hstart : P.potential (leftFace e) ≠ 0 := by
    apply Finsupp.mem_support_iff.mp
    change leftFace e ∈ P.interiorFaces
    rw [hPf,Finsupp.mem_support_iff,hpone]
    norm_num
  have hend : P.potential (leftFace (terminalGerm e w)) ≠ 0 := by
    rw [P.trace_left_potential e w hdis]
    exact hstart
  by_contra hout
  have hnot : (terminalGerm e w).1 ∉ P.vertices := by
    simpa only [hPv,List.mem_toFinset] using hout
  have hmiss := (outside_boundary_germ D hD (terminalGerm e w).1
    (terminalGerm e w).2 hu hu').1.1
  have hzero : P.potential (leftFace ((terminalGerm e w).1,(terminalGerm e w).2+1)) = 0 := by
    by_contra hz
    have hm : leftFace ((terminalGerm e w).1,(terminalGerm e w).2+1) ∈ P.interiorFaces :=
      Finsupp.mem_support_iff.mpr hz
    rw [hPf] at hm
    exact hmiss (hpS hm)
  rw [(P.off_boundary_faces _ hnot _).1] at hzero
  apply hend
  exact (P.off_boundary_faces _ hnot _).1.trans hzero

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem turnUnits_append (u w : List Bool) :
    turnUnits (u ++ w) = turnUnits u + turnUnits w := by
  simp [turnUnits]

@[simp] theorem reverse_stem_false (g : Germ) :
    reverseGerm (stemGerm g false) = advance g true := rfl

@[simp] theorem reverse_advance_true (g : Germ) :
    reverseGerm (advance g true) = stemGerm g false := by
  rw [← reverse_stem_false,reverseGerm_reverseGerm]

theorem chord_close_trace (g h e : Germ) (B w : List Bool)
    (hb : terminalGerm h (false :: B) = g)
    (he : terminalGerm e w = stemGerm h false) :
    traced e (w ++ (true :: B) ++ [true]) =
      traced e w ++ (traced h (false :: B) ++ [g.1]) := by
  simp only [traced_append,terminalGerm_append,he]
  have htr := stem_forward_trace h false B
  have htm := stem_forward_terminal h false B
  simp only [Bool.not_false] at htr htm
  rw [htr,htm,hb]
  simp [traced,List.append_assoc]

theorem chord_close_terminal (g h e : Germ) (B w : List Bool)
    (hb : terminalGerm h (false :: B) = g)
    (he : terminalGerm e w = stemGerm h false) (he' : e = advance g true) :
    terminalGerm e (w ++ (true :: B) ++ [true]) = e := by
  simp only [terminalGerm_append,he]
  have htm := stem_forward_terminal h false B
  simp only [Bool.not_false] at htm
  rw [htm,hb]
  simpa only [terminalGerm] using he'.symm

theorem chord_close_turn (g : Germ) (A B : List Bool) (e : Germ) (w : List Bool)
    (hN : (traced g ((false :: A) ++ (false :: B))).Nodup)
    (hc : terminalGerm g ((false :: A) ++ (false :: B)) = g)
    (he : e = advance g true)
    (ht : terminalGerm e w = stemGerm (terminalGerm g (false :: A)) false)
    (hwN : (traced e w).Nodup)
    (hd : ∀ v ∈ traced e w, v ∉ traced g ((false :: A) ++ (false :: B))) :
    turnUnits w + turnUnits (false :: B) + 3 = 6 ∨
      turnUnits w + turnUnits (false :: B) + 3 = -6 := by
  let h := terminalGerm g (false :: A)
  have hb : terminalGerm h (false :: B) = g := by
    exact (terminalGerm_append g (false :: A) (false :: B)).symm.trans hc
  have hN' : (g.1 :: (traced (advance g false) A ++ traced h (false :: B))).Nodup := by
    simpa only [h,traced_append,traced,terminalGerm,List.cons_append] using hN
  have hgnot : g.1 ∉ traced h (false :: B) := by
    intro hm
    exact (List.nodup_cons.mp hN').1 (List.mem_append_right _ hm)
  have hBN : (traced h (false :: B)).Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp hN').2).2.1
  have hBN' : (traced h (false :: B) ++ [g.1]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hBN,by simp,?_⟩
    intro a ha b hb hab
    have hb' := List.mem_singleton.mp hb
    exact hgnot ((hab.trans hb') ▸ ha)
  have hsub : ∀ v ∈ traced h (false :: B) ++ [g.1],
      v ∈ traced g ((false :: A) ++ (false :: B)) := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rw [traced_append]
      exact List.mem_append_right _ hv
    · have heq := List.mem_singleton.mp hv
      subst v
      simp [traced_append,traced]
  have hjoinN : (traced e (w ++ (true :: B) ++ [true])).Nodup := by
    rw [chord_close_trace g h e B w hb ht]
    apply List.nodup_append.mpr
    refine ⟨hwN,hBN',?_⟩
    intro a ha b hb hab
    subst b
    exact hd a ha (hsub a hb)
  have hjoinC := chord_close_terminal g h e B w hb ht he
  have hn : w ++ (true :: B) ++ [true] ≠ [] := by simp
  have h := simple_polygon_turning e _ hn hjoinN hjoinC
  have heq : turnUnits (w ++ (true :: B) ++ [true]) =
      turnUnits w + turnUnits (false :: B) + 3 := by
    simp [turnUnit,turnUnits]
    ring
  rwa [heq] at h

theorem cycle_chord_turn_bound (g : Germ) (A B : List Bool) (e : Germ) (w : List Bool)
    (hN : (traced g ((false :: A) ++ (false :: B))).Nodup)
    (hc : terminalGerm g ((false :: A) ++ (false :: B)) = g)
    (he : e = advance g true)
    (ht : terminalGerm e w = stemGerm (terminalGerm g (false :: A)) false)
    (hwN : (traced e w).Nodup)
    (hd : ∀ v ∈ traced e w, v ∉ traced g ((false :: A) ++ (false :: B)))
    (hturn : turnUnits ((false :: A) ++ (false :: B)) = 6)
    (hA : 0 ≤ turnUnits (false :: A)) (hB : 0 ≤ turnUnits (false :: B)) :
    -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 := by
  have h₁ := chord_close_turn g A B e w hN hc he ht hwN hd
  let h := terminalGerm g (false :: A)
  let e' := reverseGerm (terminalGerm e w)
  have hrot := closed_word_rotate g (false :: A) (false :: B) hN hc
  have hback : terminalGerm h (false :: B) = g := by
    exact (terminalGerm_append g (false :: A) (false :: B)).symm.trans hc
  have he' : e' = advance h true := by simp only [e',ht,reverse_stem_false]; rfl
  have ht' : terminalGerm e' (reverseTurns w) =
      stemGerm (terminalGerm h (false :: B)) false := by
    rw [hback]
    simp only [e',terminalGerm_reverse,he,reverse_advance_true]
  have hwN' : (traced e' (reverseTurns w)).Nodup := by
    simpa only [e',traced_reverse,List.nodup_reverse] using hwN
  have hd' : ∀ v ∈ traced e' (reverseTurns w),
      v ∉ traced h ((false :: B) ++ (false :: A)) := by
    intro v hv hmem
    have hv' : v ∈ traced e w := by simpa only [e',traced_reverse,List.mem_reverse] using hv
    apply hd v hv'
    rw [traced_append,hback] at hmem
    rw [traced_append]
    exact List.mem_append.mpr (List.mem_append.mp hmem |>.symm)
  have h₂ := chord_close_turn h B A e' (reverseTurns w) hrot.1 hrot.2.1
    he' ht' hwN' hd'
  rw [turnUnits_reverse] at h₂
  rw [turnUnits_append] at hturn
  omega



theorem faceBoundaryWord_append (S : Finset FaceIndex) (g : FaceBoundary S) (m n : ℕ) :
    faceBoundaryWord S g (m+n) = faceBoundaryWord S g m ++
      faceBoundaryWord S ((faceBoundaryNext S)^[m] g) n := by
  induction m generalizing g with
  | zero => simp [faceBoundaryWord]
  | succ m ih =>
    simp only [Nat.succ_add,faceBoundaryWord,List.cons_append,Function.iterate_succ_apply]
    rw [ih]

@[simp] theorem boundary_stem_port (v : Vertex) (k : Fin 3) :
    stemGerm (v,k+1) false = (v,k) := by
  fin_cases k <;> simp [stemGerm,unusedSlot,outgoingSlot]

@[simp] theorem boundary_inward_port (v : Vertex) (k : Fin 3) :
    advance (v,k+1) true = reverseGerm (v,k) := by
  rw [← reverse_stem_false,boundary_stem_port]

theorem convex_distinct_outer_vertices (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    (terminalGerm e.1 e.2).1 ≠ (reverseGerm e.1).1 := by
  intro hv
  have hstart := (outside_boundary_germ D hD (reverseGerm e.1).1 e.1.2 he.2.1
    (by simpa only [reverseGerm,neighbor_neighbor] using he.1)).1
  have hend := (outside_boundary_germ D hD (terminalGerm e.1 e.2).1
    (terminalGerm e.1 e.2).2 he.2.2.2 he.reverse.1).1
  rw [hv] at hend
  have hk := faceBoundary_germ_unique (starFaces D) (reverseGerm e.1).1
    ((terminalGerm e.1 e.2).2+1) (e.1.2+1) hend hstart
  have hk' : (terminalGerm e.1 e.2).2 = e.1.2 := add_right_cancel hk
  have heq : terminalGerm e.1 e.2 = reverseGerm e.1 := Prod.ext hv hk'
  apply he.distinct_ports
  rw [heq,reverseGerm_reverseGerm]

theorem boundary_chord_turn_bound (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (hg : faceBoundaryTurn (starFaces D) g.val = false)
    (i : ℕ) (hi : 0 < i) (hin : i < n)
    (hgi : faceBoundaryTurn (starFaces D) ((faceBoundaryNext (starFaces D))^[i] g).val = false)
    (e : Germ) (w : List Bool) (he : e = advance g.val true)
    (ht : terminalGerm e w = stemGerm ((faceBoundaryNext (starFaces D))^[i] g).val false)
    (hwN : (traced e w).Nodup) (hd : ∀ v ∈ traced e w, v ∈ D) :
    -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 := by
  let G := (faceBoundaryNext (starFaces D))^[i] g
  have hn : 0 < n := lt_trans hi hin
  have hperiod : (faceBoundaryNext (starFaces D))^[n] g = g := by
    apply Subtype.ext
    rwa [faceBoundaryWord_terminal] at hc
  have hend : (faceBoundaryNext (starFaces D))^[n-i] G = g := by
    simp only [G,← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel (Nat.le_of_lt hin),hperiod]
  have hAi := star_boundary_word_charge D hD g i
  have hBi := star_boundary_word_charge D hD G (n-i)
  simp only [G,hgi,hg,hend,boundaryCharge,Bool.false_eq_true,ite_false,sub_self] at hAi hBi
  obtain ⟨a,hai⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  obtain ⟨b,hbi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.sub_pos_of_lt hin))
  let A := faceBoundaryWord (starFaces D) (faceBoundaryNext (starFaces D) g) a
  let B := faceBoundaryWord (starFaces D) (faceBoundaryNext (starFaces D) G) b
  have hA : faceBoundaryWord (starFaces D) g i = false :: A := by
    rw [hai,faceBoundaryWord,hg]
  have hB : faceBoundaryWord (starFaces D) G (n-i) = false :: B := by
    rw [hbi,faceBoundaryWord,hgi]
  have hW : faceBoundaryWord (starFaces D) g n = (false :: A) ++ (false :: B) := by
    conv_lhs => rw [← Nat.add_sub_cancel' (Nat.le_of_lt hin)]
    rw [faceBoundaryWord_append,hA,hB]
  have hterminal : terminalGerm g.val (false :: A) = G.val := by
    rw [← hA,faceBoundaryWord_terminal]
  apply cycle_chord_turn_bound g.val A B e w (by rwa [← hW]) (by rwa [← hW]) he
    (by rwa [hterminal]) hwN
  · intro v hv hm
    rw [← hW] at hm
    exact star_boundary_trace_outside D g n v hm (hd v hv)
  · rw [← hW]
    exact star_boundary_cycle_turn D hD g n hn hN hc
  · rwa [← hA]
  · rwa [← hB]



theorem convex_excursion_turn_bound (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    -3 ≤ turnUnits e.2 ∧ turnUnits e.2 ≤ 3 := by
  classical
  have hs := outside_boundary_germ D hD (reverseGerm e.1).1 e.1.2 he.2.1
    (by simpa only [reverseGerm,neighbor_neighbor] using he.1)
  let g : FaceBoundary (starFaces D) := ⟨((reverseGerm e.1).1,e.1.2+1),hs.1⟩
  have hge : e.1 = advance g.val true := by
    change e.1 = advance ((reverseGerm e.1).1,e.1.2+1) true
    rw [boundary_inward_port]
    exact (reverseGerm_reverseGerm e.1).symm
  obtain ⟨n,hn,hN,hc⟩ := faceBoundary_closed_word (starFaces D) g
  obtain ⟨hwN,hwD⟩ := stopped_traced D e.1 e.2 he.2.2.1
  have hm := star_boundary_endpoint D hD g n hn hN hc hs.2 e.1 e.2 hge hwD
    he.2.2.2 he.reverse.1
  rw [faceBoundaryWord_traced,List.mem_ofFn] at hm
  obtain ⟨i,hi⟩ := hm
  have hi0 : 0 < i.val := by
    by_contra hn
    have hz : i.val = 0 := by omega
    have hv : (terminalGerm e.1 e.2).1 = (reverseGerm e.1).1 := by
      simpa only [hz,Function.iterate_zero,id_eq,g] using hi.symm
    exact convex_distinct_outer_vertices D hD e he hv
  have hu := outside_boundary_germ D hD (terminalGerm e.1 e.2).1
    (terminalGerm e.1 e.2).2 he.2.2.2 he.reverse.1
  let u : FaceBoundary (starFaces D) :=
    ⟨((terminalGerm e.1 e.2).1,(terminalGerm e.1 e.2).2+1),hu.1⟩
  have hiu : (faceBoundaryNext (starFaces D))^[i.val] g = u :=
    faceBoundary_vertex_injective (starFaces D) hi
  apply boundary_chord_turn_bound D hD g n hN hc hs.2 i.val hi0 i.isLt
    (by rw [hiu]; exact hu.2) e.1 e.2 hge _ hwN hwD
  rw [hiu]
  change terminalGerm e.1 e.2 = stemGerm
    ((terminalGerm e.1 e.2).1,(terminalGerm e.1 e.2).2+1) false
  exact (boundary_stem_port _ _).symm

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def sourceExits (D : Finset Vertex) (g : Germ) : Finset (List Bool) := by
  classical
  exact (leaves D g).filter fun w => (terminalGerm g w).1 ∉ D

def ConvexBoundaryFlux : Prop := ∀ (D : Finset Vertex) (g : Germ),
  AdmissiblyConvex D → g.1 ∈ D → (reverseGerm g).1 ∉ D →
    (∑ w ∈ sourceExits D g, wordWeight w) = 1 ∧
    (∑ w ∈ sourceExits D g, criticalActivity ^ w.length) ≤
      (Real.cos (3 * Real.pi / 8))⁻¹



def coordinateIndex (v : Vertex) (k : Fin 3) : ℤ :=
  match v with
  | .up i j => if k = 0 then 3*j+1 else if k = 1 then 3*i+1 else 3*(i+j)+2
  | .down i j => if k = 0 then 3*j+2 else if k = 1 then 3*i+2 else 3*(i+j+1)+1

theorem coordinateIndex_box_iff (lo hi : Fin 3 → ℤ) (v : Vertex) (k : Fin 3) :
    (3*lo k < coordinateIndex v k ∧ coordinateIndex v k < 3*hi k) ↔
      lo k ≤ boxIndex v k ∧ boxIndex v k < hi k := by
  cases v <;> fin_cases k <;> simp [coordinateIndex,boxIndex] <;> omega

theorem coordinateIndex_increase (v : Vertex) (k : Fin 3) :
    ∃ l : Fin 3, coordinateIndex v k < coordinateIndex (neighbor v l) k := by
  cases v <;> fin_cases k
  all_goals first
    | (refine ⟨0,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨1,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨2,?_⟩; simp [coordinateIndex,neighbor]; omega)

theorem coordinateIndex_decrease (v : Vertex) (k : Fin 3) :
    ∃ l : Fin 3, coordinateIndex (neighbor v l) k < coordinateIndex v k := by
  cases v <;> fin_cases k
  all_goals first
    | (refine ⟨0,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨1,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨2,?_⟩; simp [coordinateIndex,neighbor]; omega)

theorem Polygon.interior_maximum_principle (P : Polygon) (f : Vertex → ℤ)
    (hf : ∀ v, ∃ k : Fin 3, f v < f (neighbor v k)) (M : ℤ)
    (hbd : ∀ v ∈ P.vertices, f v < M) : ∀ v ∈ P.interior, f v < M := by
  classical
  intro v hv
  let R := P.interior.image f
  have hvR : f v ∈ R := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have hne : R.Nonempty := ⟨f v,hvR⟩
  let m := R.max' hne
  obtain ⟨u,hu,hum⟩ := Finset.mem_image.mp (R.max'_mem hne)
  obtain ⟨k,hk⟩ := hf u
  have hn : neighbor u k ∉ P.interior := by
    intro hn
    have hle := R.le_max' _ (Finset.mem_image.mpr ⟨neighbor u k,hn,rfl⟩)
    change f (neighbor u k) ≤ m at hle
    change f u = m at hum
    omega
  have hb := P.interior_exit_on_boundary u k hu hn
  have hbound := hbd _ hb
  have hle := R.le_max' (f v) hvR
  change f v ≤ m at hle
  change f u = m at hum
  omega

theorem admissiblyConvex_filled (D : Finset Vertex) (hD : AdmissiblyConvex D) : Filled D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  intro P hP v hv
  apply (hbox v).mpr
  intro k
  apply (coordinateIndex_box_iff lo hi v k).mp
  have hp : P.vertices ⊆ D := (mem_polygons D P).mp hP
  have hbd (u : Vertex) (hu : u ∈ P.vertices) :
      3*lo k < coordinateIndex u k ∧ coordinateIndex u k < 3*hi k :=
    (coordinateIndex_box_iff lo hi u k).mpr ((hbox u).mp (hp hu) k)
  have hh := P.interior_maximum_principle (fun u => coordinateIndex u k)
    (fun u => coordinateIndex_increase u k) (3*hi k) (fun u hu => (hbd u hu).2) v hv
  have hl := P.interior_maximum_principle (fun u => -coordinateIndex u k)
    (fun u => by obtain ⟨l,hl⟩ := coordinateIndex_decrease u k; exact ⟨l,by omega⟩)
    (-3*lo k) (fun u hu => by have := (hbd u hu).1; omega) v hv
  omega

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem rayLeaves_balance (D : Finset Vertex) (v : Vertex) :
    (∑ e ∈ rayLeaves D v, wordWeight e.2) = 3 := by
  rw [rayLeaves,sum_record_fibers]
  simp only [leaf_balance,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num

theorem rayExits_filter (D : Finset Vertex) (v : Vertex) :
    rayExits D v = (rayLeaves D v).filter (fun e => (stemEnd v e).1 ∉ D) := rfl

theorem rayLeaves_split (D : Finset Vertex) (v : Vertex) (hv : v ∈ D) :
    (∑ e ∈ rayLeaves D v, wordWeight e.2) =
      (∑ e ∈ rayExits D v, wordWeight e.2) +
      (∑ e ∈ rayReturns D v, wordWeight e.2) +
      (∑ e ∈ rayCollisions D v, wordWeight e.2) := by
  classical
  rw [rayExits_filter,rayReturns,rayCollisions]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  change wordWeight e.2 = (if (stemEnd v e).1 ∉ D then _ else _) +
    (if (stemEnd v e).1 = v then _ else _) + _
  by_cases hD : (stemEnd v e).1 ∈ D
  · by_cases hEq : (stemEnd v e).1 = v <;> simp [hD,hEq,hv]
  · have hEq : (stemEnd v e).1 ≠ v := fun h => hD (h.symm ▸ hv)
    simp [hD,hEq]

theorem complex_visit_balance (D : Finset Vertex) (v : Vertex) (hD : Filled D) (hv : v ∈ D) :
    (3 : ℂ) = visitSum D v +
      (∑ P ∈ polygons D, if v ∈ P.vertices then
        (2 : ℂ) * (criticalActivity : ℂ) ^ (P.length - 1) *
          (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ) else 0) +
      (∑ P ∈ polygons D, if v ∈ P.interior then
        -2 * (criticalActivity : ℂ) ^ P.length * visitSum P.interior v else 0) := by
  have h := rayLeaves_split D v hv
  rw [rayLeaves_balance,rayExits_eq_visitSum D v hD hv,
    return_sum_polygons D v hv,collision_sum_polygons D v hD] at h
  exact h

theorem finite_visit_recursion : FiniteVisitRecursion := by
  classical
  intro D v hD hv
  have h := congrArg Complex.reAddGroupHom (complex_visit_balance D v hD hv)
  simp only [map_add,map_sum,Complex.coe_reAddGroupHom,← Complex.ofReal_pow] at h
  have hr : (∑ P ∈ polygons D, (if v ∈ P.vertices then
      (2 : ℂ) * (criticalActivity ^ (P.length - 1) : ℝ) *
        (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ) else 0).re) =
    -(∑ P ∈ polygons D, if v ∈ P.vertices then
      2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro P hP
    split_ifs <;> simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,
      Complex.mul_re,Complex.mul_im,show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,mul_zero,zero_mul,sub_zero,add_zero]
    all_goals ring
  have hc : (∑ P ∈ polygons D, (if v ∈ P.interior then
      -(2 : ℂ) * (criticalActivity ^ P.length : ℝ) * visitSum P.interior v else 0).re) =
    -(∑ P ∈ polygons D, if v ∈ P.interior then
      2 * criticalActivity ^ P.length * visitMass P.interior v else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro P hP
    split_ifs <;> simp only [visitMass,Complex.mul_re,Complex.mul_im,Complex.neg_re,
      Complex.neg_im,show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
      Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,mul_zero,zero_mul,
      neg_zero,sub_zero,add_zero]
    all_goals ring
  rw [hr,hc] at h
  change _ = visitMass D v + _ + _ at h
  norm_num only [show (3 : ℂ).re = 3 from rfl] at h
  linarith


theorem criticalActivity_pos : 0 < criticalActivity := by
  unfold criticalActivity
  exact inv_pos.mpr (mul_pos (by norm_num) critical_cos_pos)

theorem Polygon.ccwTurn_cases (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    P.ccwTurn v = Real.pi / 3 ∨ P.ccwTurn v = -(Real.pi / 3) := by
  obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hw.1
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator (v,k) (b :: u)
    (by simp) hw.2.1 hw.2.2.1
  have he := P.ccwTurn_traversal (v,k) b u hw p ε hp hε hvals
  rcases hε with rfl | rfl <;> cases b <;> simp [turnUnit] at he <;> simp [he]

theorem through_cos_pos (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    0 < -Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) := by
  have hpi := Real.pi_pos
  rcases P.ccwTurn_cases v hv with h | h
  · rw [h,show (3 / 8 : ℝ) * (2 * Real.pi - Real.pi / 3) = Real.pi - 3 * Real.pi / 8 by ring,
      Real.cos_pi_sub,neg_neg]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  · rw [h,show (3 / 8 : ℝ) * (2 * Real.pi - -(Real.pi / 3)) = Real.pi - Real.pi / 8 by ring,
      Real.cos_pi_sub,neg_neg]
    exact critical_cos_pos

theorem recursion_coefficients_positive (P : Polygon) :
    0 < 2 * criticalActivity ^ P.length ∧ ∀ v ∈ P.vertices,
      0 < 2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) := by
  constructor
  · exact mul_pos (by norm_num) (pow_pos criticalActivity_pos _)
  · intro v hv
    exact mul_pos (mul_pos (by norm_num) (pow_pos criticalActivity_pos _)) (through_cos_pos P v hv)

theorem visitMass_ge_three (D : Finset Vertex) (v : Vertex) (hD : Filled D) (hv : v ∈ D) :
    3 ≤ visitMass D v := by
  classical
  induction hn : D.card using Nat.strong_induction_on generalizing D with
  | h n ih =>
      rw [finite_visit_recursion D v hD hv]
      have hp : 0 ≤ ∑ P ∈ polygons D, if v ∈ P.vertices then
          2 * criticalActivity ^ (P.length - 1) *
            (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) else 0 := by
        apply Finset.sum_nonneg
        intro P hP
        split_ifs with hvP
        · exact (recursion_coefficients_positive P).2 v hvP |>.le
        · exact le_rfl
      have hi : 0 ≤ ∑ P ∈ polygons D, if v ∈ P.interior then
          2 * criticalActivity ^ P.length * visitMass P.interior v else 0 := by
        apply Finset.sum_nonneg
        intro P hP
        split_ifs with hvP
        · have hl : P.interior.card < n := hn ▸ P.interior_card_lt D hD hP
          have hmass := ih P.interior.card hl P.interior P.interior_filled hvP rfl
          exact mul_nonneg (recursion_coefficients_positive P).1.le (by linarith)
        · exact le_rfl
      linarith

theorem polygons_mono {D E : Finset Vertex} (hDE : D ⊆ E) : polygons D ⊆ polygons E := by
  intro P hP
  exact (mem_polygons E P).mpr ((mem_polygons D P).mp hP |>.trans hDE)

theorem visitMass_mono (D E : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hE : Filled E) (hDE : D ⊆ E) (hv : v ∈ D) :
    visitMass D v ≤ visitMass E v := by
  classical
  rw [finite_visit_recursion D v hD hv,finite_visit_recursion E v hE (hDE hv)]
  apply add_le_add
  · apply add_le_add le_rfl
    apply Finset.sum_le_sum_of_subset_of_nonneg (polygons_mono hDE)
    intro P hP hn
    split_ifs with hvP
    · exact (recursion_coefficients_positive P).2 v hvP |>.le
    · exact le_rfl
  · apply Finset.sum_le_sum_of_subset_of_nonneg (polygons_mono hDE)
    intro P hP hn
    split_ifs with hvP
    · have hmass := visitMass_ge_three P.interior v P.interior_filled hvP
      exact mul_nonneg (recursion_coefficients_positive P).1.le (by linarith)
    · exact le_rfl



theorem wordWeight_re (w : List Bool) : (wordWeight w).re =
    criticalActivity ^ w.length * Real.cos (Real.pi / 8 * (turnUnits w : ℝ)) := by
  rw [wordWeight_turnUnits]
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]

theorem wordWeight_re_le (w : List Bool) :
    (wordWeight w).re ≤ criticalActivity ^ w.length := by
  rw [wordWeight_re]
  exact mul_le_of_le_one_right (pow_nonneg criticalActivity_pos.le _) (Real.cos_le_one _)

theorem bounded_turn_cos (m : ℤ) (hm : -3 ≤ m ∧ m ≤ 3) :
    Real.cos (3 * Real.pi / 8) ≤ Real.cos (Real.pi / 8 * (m : ℝ)) := by
  have hlow : -(3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
  have hhigh : (m : ℝ) ≤ 3 := by exact_mod_cast hm.2
  have habs : |Real.pi / 8 * (m : ℝ)| ≤ 3 * Real.pi / 8 := by
    apply abs_le.mpr
    constructor <;> nlinarith [Real.pi_pos]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi / 8 * (m : ℝ)))
    (show 3 * Real.pi / 8 ≤ Real.pi by linarith [Real.pi_pos]) habs
  simpa only [Real.cos_abs] using h

theorem convex_wordWeight_re_lower (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    Real.cos (3 * Real.pi / 8) * criticalActivity ^ e.2.length ≤ (wordWeight e.2).re := by
  rw [wordWeight_re,mul_comm (Real.cos _)]
  exact mul_le_mul_of_nonneg_left
    (bounded_turn_cos (turnUnits e.2) (convex_excursion_turn_bound D hD e he))
    (pow_nonneg criticalActivity_pos.le _)

theorem visitMass_excursion_upper (D : Finset Vertex) (v : Vertex) :
    visitMass D v ≤ excursionMass D v := by
  classical
  simp only [visitMass,visitSum,excursionMass,Complex.re_sum]
  apply Finset.sum_le_sum
  intro e he
  split_ifs <;> try simp only [Complex.zero_re,le_refl]
  exact wordWeight_re_le _

theorem visitMass_excursion_lower (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) :
    Real.cos (3 * Real.pi / 8) * excursionMass D v ≤ visitMass D v := by
  classical
  simp only [visitMass,visitSum,excursionMass,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  split_ifs <;> try simp only [mul_zero,Complex.zero_re,le_refl]
  exact convex_wordWeight_re_lower D hD e ((mem_excursions D e).mp he)

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem mem_sourceExits (D : Finset Vertex) (g : Germ) (w : List Bool) :
    w ∈ sourceExits D g ↔ Stopped D g w ∧ (terminalGerm g w).1 ∉ D := by
  classical
  simp [sourceExits,mem_leaves_iff]

theorem boundary_source_flux (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    (∑ w ∈ sourceExits D g, wordWeight w) = 1 := by
  have h := exit_add_collision D g
  rw [(boundary_collision_cancellation D g hD hg).1,add_zero] at h
  simpa only [sourceExits,Finset.sum_filter,exitSum] using h

theorem boundary_source_weight_bound (D : Finset Vertex) (g : Germ)
    (hD : AdmissiblyConvex D) (hg : g.1 ∈ D) (hg' : (reverseGerm g).1 ∉ D) :
    (∑ w ∈ sourceExits D g, criticalActivity ^ w.length) ≤
      (Real.cos (3 * Real.pi / 8))⁻¹ := by
  have hflux := boundary_source_flux D g (admissiblyConvex_filled D hD) hg'
  have hreal := congrArg Complex.re hflux
  rw [Complex.re_sum,Complex.one_re] at hreal
  have hlower : Real.cos (3 * Real.pi / 8) *
      (∑ w ∈ sourceExits D g, criticalActivity ^ w.length) ≤ 1 := by
    rw [← hreal,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
    exact convex_wordWeight_re_lower D hD (g,w) ⟨hg,hg',hs,ht⟩
  have hpos : 0 < Real.cos (3 * Real.pi / 8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hpos).mpr
  rwa [mul_comm]

theorem convex_boundary_flux : ConvexBoundaryFlux := by
  intro D g hD hg hg'
  exact ⟨boundary_source_flux D g (admissiblyConvex_filled D hD) hg',
    boundary_source_weight_bound D g hD hg hg'⟩


def bottomSource : Germ := (.up 0 0,0)

def InStrip (h : ℕ) (v : Vertex) : Prop := 0 ≤ boxIndex v 0 ∧ boxIndex v 0 < (h : ℤ)

noncomputable def reachesDistance (t : ℝ) (w : List Bool) : Prop :=
  ∃ v ∈ traced bottomSource w, t ≤ |(position v).1|

noncomputable def lateralMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact ∑ w ∈ sourceExits D bottomSource,
    if reachesDistance t w then criticalActivity ^ w.length else 0

noncomputable def lateralLengthMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact ∑ w ∈ sourceExits D bottomSource,
    if reachesDistance t w then (w.length : ℝ) * criticalActivity ^ w.length else 0

def FiniteLateralTail : Prop := ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (h : ℕ) (D : Finset Vertex), 1 ≤ h → AdmissiblyConvex D →
    bottomSource.1 ∈ D → (∀ v ∈ D, InStrip h v) → ∀ t : ℝ, 0 ≤ t →
    lateralMass D t ≤ C * Real.exp (-c * t / (h+1)) ∧
    lateralLengthMass D t ≤ C * (h+1) * (h+t+1) * Real.exp (-c * t / (h+1))



def directionCode (g : Germ) : ℤ := match g.1 with
  | .up _ _ => if g.2 = 0 then 0 else if g.2 = 1 then 2 else 4
  | .down _ _ => if g.2 = 0 then 3 else if g.2 = 1 then 5 else 1

theorem advance_direction (g : Germ) (b : Bool) :
    (directionCode (advance g b) - directionCode g - turnUnit b) % 6 = 0 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    rfl

theorem terminal_direction (g : Germ) (w : List Bool) :
    (directionCode (terminalGerm g w) - directionCode g - turnUnits w) % 6 = 0 := by
  induction w generalizing g with
  | nil => simp [terminalGerm,turnUnits]
  | cons b w ih =>
    have ha := advance_direction g b
    have ht := ih (advance g b)
    simp only [terminalGerm,turnUnits_cons]
    omega

theorem right_cut_direction_one (v : Vertex) (k : Fin 3) (A : ℤ)
    (hv : boxIndex v 1 < A) (hu : A ≤ boxIndex (neighbor v k) 1) :
    directionCode (neighbor v k,k) = 4 := by
  cases v <;> fin_cases k <;>
    simp [boxIndex,neighbor,directionCode] at * <;> omega

theorem right_cut_direction_two (v : Vertex) (k : Fin 3) (A : ℤ)
    (hv : boxIndex v 2 < A) (hu : A ≤ boxIndex (neighbor v k) 2) :
    directionCode (neighbor v k,k) = 5 := by
  cases v <;> fin_cases k <;>
    simp [boxIndex,neighbor,directionCode] at * <;> omega

theorem convex_source_direction_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (w : List Bool) (hw : w ∈ sourceExits D bottomSource) :
    (directionCode (terminalGerm bottomSource w) = 4 → turnUnits w = -2) ∧
    (directionCode (terminalGerm bottomSource w) = 5 → turnUnits w = -1) := by
  have hb := convex_excursion_turn_bound D hD (bottomSource,w)
    ⟨hg,hg',(mem_sourceExits D bottomSource w).mp hw⟩
  change -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 at hb
  have hm := terminal_direction bottomSource w
  rw [show directionCode bottomSource = 0 from rfl,sub_zero] at hm
  constructor <;> intro h <;> rw [h] at hm <;> omega

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def upperCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) : Finset Vertex :=
  D.filter fun v => boxIndex v k < A

@[simp] theorem mem_upperCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) (v : Vertex) :
    v ∈ upperCut D k A ↔ v ∈ D ∧ boxIndex v k < A := by
  simp [upperCut]

theorem upperCut_subset (D : Finset Vertex) (k : Fin 3) (A : ℤ) : upperCut D k A ⊆ D :=
  Finset.filter_subset _ _

theorem admissiblyConvex_of_box (D : Finset Vertex) (lo hi : Fin 3 → ℤ)
    (h : ∀ v, v ∈ D ↔ BoxMem lo hi v) : AdmissiblyConvex D := by
  refine ⟨lo,hi,fun v => ?_⟩
  rw [h]
  apply forall_congr'
  intro k
  obtain ⟨a,ha,ha',he⟩ := tilingCoordinate_index v k
  rw [he]
  exact (integer_bounds_fraction _ _ _ _ ha ha').symm

theorem upperCut_convex (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (k : Fin 3) (A : ℤ) : AdmissiblyConvex (upperCut D k A) := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  apply admissiblyConvex_of_box _ lo (fun l => if l = k then min (hi l) A else hi l)
  intro v
  simp only [mem_upperCut,hbox,BoxMem]
  constructor
  · rintro ⟨hv,hA⟩ l
    by_cases hl : l = k
    · subst l; simpa only [ite_true,lt_min_iff] using ⟨(hv k).1,(hv k).2,hA⟩
    · simpa only [hl,ite_false] using hv l
  · intro hv
    constructor
    · intro l
      by_cases hl : l = k
      · subst l
        have hh := hv k
        simp only [ite_true,lt_min_iff] at hh
        exact ⟨hh.1,hh.2.1⟩
      · simpa only [hl,ite_false] using hv l
    · have hh := hv k
      simp only [ite_true,lt_min_iff] at hh
      exact hh.2.2

theorem sourceExits_restrict_iff (D E : Finset Vertex) (hED : E ⊆ D)
    (g : Germ) (w : List Bool) (hw : w ∈ sourceExits D g) :
    w ∈ sourceExits E g ↔ ∀ v ∈ traced g w, v ∈ E := by
  obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
  constructor
  · intro he
    exact (stopped_traced E g w ((mem_sourceExits E g w).mp he).1).2
  · intro he
    have hn := (stopped_traced D g w hs).1
    have hout : (terminalGerm g w).1 ∉ E := fun hm => ht (hED hm)
    exact (mem_sourceExits E g w).mpr ⟨stopped_of_trace E g w hn he hout,hout⟩

theorem new_exit_terminal_inside (D E : Finset Vertex) (hED : E ⊆ D)
    (g : Germ) (w : List Bool) (hw : w ∈ sourceExits E g \ sourceExits D g) :
    (terminalGerm g w).1 ∈ D := by
  classical
  obtain ⟨he,hd⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨hs,ht⟩ := (mem_sourceExits E g w).mp he
  obtain ⟨hn,hm⟩ := stopped_traced E g w hs
  by_contra hout
  apply hd
  exact (mem_sourceExits D g w).mpr
    ⟨stopped_of_trace D g w hn (fun v hv => hED (hm v hv)) hout,hout⟩

theorem flux_subtraction (D E : Finset Vertex) (g : Germ)
    (hD : Filled D) (hE : Filled E)
    (hgD : (reverseGerm g).1 ∉ D) (hgE : (reverseGerm g).1 ∉ E) :
    (∑ w ∈ sourceExits D g \ sourceExits E g, wordWeight w) =
      ∑ w ∈ sourceExits E g \ sourceExits D g, wordWeight w := by
  apply sub_eq_zero.mp
  rw [Finset.sum_sdiff_sub_sum_sdiff,boundary_source_flux D g hD hgD,
    boundary_source_flux E g hE hgE,sub_self]

theorem mem_lost_upperCut (D : Finset Vertex) (g : Germ) (k : Fin 3) (A : ℤ)
    (w : List Bool) : w ∈ sourceExits D g \ sourceExits (upperCut D k A) g ↔
      w ∈ sourceExits D g ∧ ∃ v ∈ traced g w, A ≤ boxIndex v k := by
  classical
  simp only [Finset.mem_sdiff]
  by_cases hw : w ∈ sourceExits D g
  · simp only [hw,true_and,sourceExits_restrict_iff D _ (upperCut_subset D k A) g w hw]
    have hm := (stopped_traced D g w ((mem_sourceExits D g w).mp hw).1).2
    simp only [mem_upperCut,not_forall,not_and,not_lt]
    constructor
    · rintro ⟨v,hv,hnot⟩
      exact ⟨v,hv,hnot (hm v hv)⟩
    · rintro ⟨v,hv,hA⟩
      exact ⟨v,hv,fun _ => hA⟩
  · simp [hw]

theorem bottomSource_outside_of_strip (h : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) : (reverseGerm bottomSource).1 ∉ D := by
  intro hv
  have hh := (hstrip _ hv).1
  norm_num [bottomSource,reverseGerm,neighbor,boxIndex] at hh

theorem bottomSource_mem_upperCut (D : Finset Vertex) (hg : bottomSource.1 ∈ D)
    (k : Fin 3) (A : ℤ) (hA : 0 < A) : bottomSource.1 ∈ upperCut D k A := by
  apply (mem_upperCut _ _ _ _).mpr
  refine ⟨hg,?_⟩
  fin_cases k <;> simpa [bottomSource,boxIndex] using hA

theorem new_upperCut_direction (D : Finset Vertex) (k : Fin 3) (A : ℤ)
    (hg : bottomSource.1 ∈ upperCut D k A) (w : List Bool)
    (hw : w ∈ sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :
    boxIndex (reverseGerm (terminalGerm bottomSource w)).1 k < A ∧
      A ≤ boxIndex (terminalGerm bottomSource w).1 k := by
  classical
  have he := (mem_sourceExits _ _ _).mp (Finset.mem_sdiff.mp hw).1
  have hn : w ≠ [] := by
    intro h
    exact he.2 (by simpa [h,terminalGerm] using hg)
  have hpred := (stopped_traced _ _ _ he.1).2 _ (reverse_first_mem bottomSource w hn)
  have hu := new_exit_terminal_inside D _ (upperCut_subset D k A) _ _ hw
  exact ⟨((mem_upperCut _ _ _ _).mp hpred).2,by
    by_contra hx
    exact he.2 ((mem_upperCut _ _ _ _).mpr ⟨hu,by omega⟩)⟩

theorem new_upperCut_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (A : ℤ) (hA : 0 < A) (k : Fin 3) (w : List Bool)
    (hw : w ∈ sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :
    (k = 1 → turnUnits w = -2) ∧ (k = 2 → turnUnits w = -1) := by
  have hmem := bottomSource_mem_upperCut D hg k A hA
  obtain ⟨hl,hu⟩ := new_upperCut_direction D k A hmem w hw
  have ht := convex_source_direction_turn _ (upperCut_convex D hD k A) hmem
    (fun hm => hg' (upperCut_subset D k A hm)) w (Finset.mem_sdiff.mp hw).1
  constructor
  · intro hk; subst k
    apply ht.1
    have hd := right_cut_direction_one (reverseGerm (terminalGerm bottomSource w)).1
      (terminalGerm bottomSource w).2 A hl
      (by simpa only [reverseGerm,neighbor_neighbor] using hu)
    simpa only [reverseGerm,neighbor_neighbor] using hd
  · intro hk; subst k
    apply ht.2
    have hd := right_cut_direction_two (reverseGerm (terminalGerm bottomSource w)).1
      (terminalGerm bottomSource w).2 A hl
      (by simpa only [reverseGerm,neighbor_neighbor] using hu)
    simpa only [reverseGerm,neighbor_neighbor] using hd

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def positiveWordMass (S : Finset (List Bool)) : ℝ :=
  ∑ w ∈ S, criticalActivity ^ w.length
noncomputable def phasedWordMass (S : Finset (List Bool)) : ℂ :=
  ∑ w ∈ S, wordWeight w
noncomputable def phase (a : ℝ) : ℂ := Complex.exp ((a : ℂ) * Complex.I)

@[simp] theorem phase_norm (a : ℝ) : ‖phase a‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I a

theorem phase_add (a b : ℝ) : phase (a+b) = phase a * phase b := by
  simp only [phase,Complex.ofReal_add,add_mul,Complex.exp_add]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem wordWeight_norm (w : List Bool) :
    ‖wordWeight w‖ = criticalActivity ^ w.length := by
  rw [wordWeight_turnUnits,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos criticalActivity_pos]

theorem positiveWordMass_nonneg (S : Finset (List Bool)) : 0 ≤ positiveWordMass S :=
  Finset.sum_nonneg fun _ _ => pow_nonneg criticalActivity_pos.le _

theorem phasedWordMass_norm_le (S : Finset (List Bool)) :
    ‖phasedWordMass S‖ ≤ positiveWordMass S := by
  simpa only [phasedWordMass,positiveWordMass,wordWeight_norm] using norm_sum_le S wordWeight

theorem positiveWordMass_mono {S T : Finset (List Bool)} (h : S ⊆ T) :
    positiveWordMass S ≤ positiveWordMass T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => pow_nonneg criticalActivity_pos.le _)

noncomputable def rayContraction : ℝ :=
  (1 + Real.cos (3*Real.pi/8) * Real.sin (Real.pi/8))⁻¹

theorem rayContraction_range : 0 < rayContraction ∧ rayContraction < 1 := by
  have hc : 0 < Real.cos (3*Real.pi/8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi/8) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hd := mul_pos hc hs
  constructor
  · exact inv_pos.mpr (by linarith)
  · apply (inv_lt_one₀ (by linarith : 0 < 1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))).mpr
    linarith

theorem separated_rays_contract (S T : Finset (List Bool)) (hTS : T ⊆ S)
    (hlower : Real.cos (3*Real.pi/8) * positiveWordMass T ≤ (phasedWordMass T).re)
    (a b : ℝ) (hb : 0 ≤ b)
    (hS : phasedWordMass S = (a : ℂ) * phase (-Real.pi/8))
    (hT : phasedWordMass T = (b : ℂ) * phase (-Real.pi/4)) :
    positiveWordMass T ≤ rayContraction * positiveWordMass S := by
  have halpha : Real.pi/8 + -Real.pi/4 = -Real.pi/8 := by ring
  have hzero : Real.pi/8 + -Real.pi/8 = 0 := by ring
  have hrotate : phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T) =
      (a : ℂ) - (b : ℂ) * phase (-Real.pi/8) := by
    rw [hS,hT,mul_sub]
    have h1 := phase_add (Real.pi/8) (-Real.pi/8)
    have h2 := phase_add (Real.pi/8) (-Real.pi/4)
    rw [hzero,phase_zero] at h1
    rw [halpha] at h2
    calc
      _ = (a : ℂ) * (phase (Real.pi/8)*phase (-Real.pi/8)) -
          (b : ℂ) * (phase (Real.pi/8)*phase (-Real.pi/4)) := by ring
      _ = _ := by rw [← h1,← h2,mul_one]
  have him : (phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)).im =
      b * Real.sin (Real.pi/8) := by
    rw [hrotate]
    have hp : (phase (-Real.pi/8)).im = -Real.sin (Real.pi/8) := by
      unfold phase
      rw [Complex.exp_ofReal_mul_I_im,neg_div,Real.sin_neg]
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,hp,zero_sub,zero_mul,add_zero,mul_neg,neg_neg]
  have hnorm : b * Real.sin (Real.pi/8) ≤ ‖phasedWordMass S - phasedWordMass T‖ := by
    calc
      _ ≤ |(phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)).im| := by
        rw [him]; exact le_abs_self _
      _ ≤ ‖phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)‖ :=
        Complex.abs_im_le_norm _
      _ = _ := by rw [norm_mul,phase_norm,one_mul]
  have hbnd : Real.cos (3*Real.pi/8) * positiveWordMass T ≤ b := by
    calc
      _ ≤ (phasedWordMass T).re := hlower
      _ ≤ ‖phasedWordMass T‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ = b := by rw [hT,norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
  have hmass : positiveWordMass (S \ T) + positiveWordMass T = positiveWordMass S :=
    Finset.sum_sdiff hTS
  have hdiff : phasedWordMass S - phasedWordMass T = phasedWordMass (S \ T) :=
    (Finset.sum_sdiff_eq_sub hTS).symm
  rw [hdiff] at hnorm
  have hnorm' := phasedWordMass_norm_le (S \ T)
  have hs : 0 ≤ Real.sin (Real.pi/8) := (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).le
  have hprod := mul_le_mul_of_nonneg_right hbnd hs
  have hfinal : (1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))*positiveWordMass T ≤
      positiveWordMass S := by nlinarith
  change _ ≤ (1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))⁻¹ * _
  have hd : 0 < 1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8) := by
    have hc : 0 ≤ Real.cos (3*Real.pi/8) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos]
    nlinarith [mul_nonneg hc hs]
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hfinal)

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def lostCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) : Finset (List Bool) :=
  sourceExits D bottomSource \ sourceExits (upperCut D k A) bottomSource

noncomputable def rightIndexMass (D : Finset Vertex) (A : ℤ) : ℝ :=
  positiveWordMass (lostCut D 1 A)

theorem phasedMass_constant_turn (S : Finset (List Bool)) (m : ℤ)
    (h : ∀ w ∈ S, turnUnits w = m) :
    phasedWordMass S = (positiveWordMass S : ℂ) * phase (Real.pi/8 * (m : ℝ)) := by
  simp only [phasedWordMass,positiveWordMass,Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [wordWeight_turnUnits,h w hw,Complex.ofReal_pow]
  rfl

theorem lostCut_phases (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (A : ℤ) (hA : 0 < A) :
    (∃ b : ℝ, 0 ≤ b ∧ phasedWordMass (lostCut D 1 A) = (b : ℂ)*phase (-Real.pi/4)) ∧
    (∃ a : ℝ, 0 ≤ a ∧ phasedWordMass (lostCut D 2 A) = (a : ℂ)*phase (-Real.pi/8)) := by
  have hflux (k : Fin 3) : phasedWordMass (lostCut D k A) =
      phasedWordMass (sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :=
    flux_subtraction D _ bottomSource (admissiblyConvex_filled D hD)
      (admissiblyConvex_filled _ (upperCut_convex D hD k A)) hg'
      (fun hm => hg' (upperCut_subset D k A hm))
  constructor
  · refine ⟨positiveWordMass (sourceExits (upperCut D 1 A) bottomSource \ sourceExits D bottomSource),
      positiveWordMass_nonneg _,?_⟩
    rw [hflux 1,phasedMass_constant_turn _ (-2) (fun w hw =>
      (new_upperCut_turn D hD hg hg' A hA 1 w hw).1 rfl)]
    congr 2
    push_cast
    ring
  · refine ⟨positiveWordMass (sourceExits (upperCut D 2 A) bottomSource \ sourceExits D bottomSource),
      positiveWordMass_nonneg _,?_⟩
    rw [hflux 2,phasedMass_constant_turn _ (-1) (fun w hw =>
      (new_upperCut_turn D hD hg hg' A hA 2 w hw).2 rfl)]
    congr 2
    push_cast
    ring

theorem strip_index_bounds (h : ℕ) (v : Vertex) (hv : InStrip h v) :
    boxIndex v 1 ≤ boxIndex v 2 ∧ boxIndex v 2 ≤ boxIndex v 1 + (h : ℤ) := by
  cases v <;> simp [InStrip,boxIndex] at * <;> omega

theorem position_index (v : Vertex) :
    (position v).1 = ((boxIndex v 1 : ℝ) + (boxIndex v 2 : ℝ)) / 2 := by
  cases v <;> simp [position,boxIndex] <;> ring

theorem lostCut_nested (h : ℕ) (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v)
    (A : ℤ) : lostCut D 1 A ⊆ lostCut D 2 A ∧ lostCut D 2 A ⊆ lostCut D 1 (A-h) := by
  have hm (k : Fin 3) (B : ℤ) (w : List Bool) : w ∈ lostCut D k B ↔
      w ∈ sourceExits D bottomSource ∧ ∃ v ∈ traced bottomSource w, B ≤ boxIndex v k :=
    mem_lost_upperCut D bottomSource k B w
  constructor
  · intro w hw
    obtain ⟨he,v,hv,hA⟩ := (hm 1 A w).mp hw
    have hd := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := strip_index_bounds h v (hstrip v hd)
    exact (hm 2 A w).mpr ⟨he,v,hv,by omega⟩
  · intro w hw
    obtain ⟨he,v,hv,hA⟩ := (hm 2 A w).mp hw
    have hd := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := strip_index_bounds h v (hstrip v hd)
    exact (hm 1 (A-h) w).mpr ⟨he,v,hv,by omega⟩

theorem lostCut_real_lower (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (k : Fin 3) (A : ℤ) :
    Real.cos (3*Real.pi/8)*positiveWordMass (lostCut D k A) ≤
      (phasedWordMass (lostCut D k A)).re := by
  rw [phasedWordMass,Complex.re_sum,positiveWordMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have he := (Finset.mem_sdiff.mp hw).1
  exact convex_wordWeight_re_lower D hD (bottomSource,w)
    ⟨hg,hg',(mem_sourceExits _ _ _).mp he⟩

theorem rightIndexMass_step (h : ℕ) (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hstrip : ∀ v ∈ D, InStrip h v)
    (A : ℤ) (hA : 0 < A) :
    rightIndexMass D A ≤ rayContraction * rightIndexMass D (A-h) := by
  have hout := bottomSource_outside_of_strip h D hstrip
  obtain ⟨⟨b,hb,hb'⟩,⟨a,_,ha'⟩⟩ := lostCut_phases D hD hg hout A hA
  have hn := lostCut_nested h D hstrip A
  have hc := separated_rays_contract (lostCut D 2 A) (lostCut D 1 A) hn.1
    (lostCut_real_lower D hD hg hout 1 A) a b hb ha' hb'
  exact hc.trans (mul_le_mul_of_nonneg_left (positiveWordMass_mono hn.2) rayContraction_range.1.le)

theorem rightIndexMass_total_bound (h : ℕ) (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hstrip : ∀ v ∈ D, InStrip h v) (A : ℤ) :
    rightIndexMass D A ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
  apply (positiveWordMass_mono (show lostCut D 1 A ⊆ sourceExits D bottomSource from
    Finset.sdiff_subset)).trans
  exact boundary_source_weight_bound D bottomSource hD hg (bottomSource_outside_of_strip h D hstrip)

theorem rightIndexMass_geometric (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (n : ℕ) :
    rightIndexMass D ((n : ℤ)*h) ≤ (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := by
  induction n with
  | zero => simpa using rightIndexMass_total_bound h D hD hg hstrip 0
  | succ n ih =>
    have hA : 0 < ((n+1 : ℕ) : ℤ)*(h : ℤ) := by positivity
    have hs := rightIndexMass_step h D hD hg hstrip _ hA
    have hi : ((n+1 : ℕ) : ℤ)*(h : ℤ) - h = (n : ℤ)*h := by push_cast; ring
    rw [hi] at hs
    calc
      _ ≤ rayContraction * rightIndexMass D ((n : ℤ)*h) := hs
      _ ≤ rayContraction * ((Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n) :=
        mul_le_mul_of_nonneg_left ih rayContraction_range.1.le
      _ = _ := by rw [pow_succ]; ring

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def mirrorVertex : Vertex → Vertex
  | .up i j => .up (-i-j) j
  | .down i j => .down (-i-j-1) j

def mirrorSlot (k : Fin 3) : Fin 3 := if k = 0 then 0 else if k = 1 then 2 else 1

def mirrorGerm (g : Germ) : Germ := (mirrorVertex g.1,mirrorSlot g.2)
def mirrorWord (w : List Bool) : List Bool := w.map Bool.not

@[simp] theorem mirrorVertex_invol (v : Vertex) : mirrorVertex (mirrorVertex v) = v := by
  cases v <;> simp [mirrorVertex]
  omega

@[simp] theorem mirrorSlot_invol (k : Fin 3) : mirrorSlot (mirrorSlot k) = k := by
  fin_cases k <;> rfl

@[simp] theorem mirrorGerm_invol (g : Germ) : mirrorGerm (mirrorGerm g) = g := by
  simp [mirrorGerm]

@[simp] theorem mirrorWord_invol (w : List Bool) : mirrorWord (mirrorWord w) = w := by
  simp [mirrorWord,List.map_map,Function.comp_def]

theorem mirrorVertex_injective : Function.Injective mirrorVertex :=
  Function.Involutive.injective mirrorVertex_invol

theorem mirrorWord_injective : Function.Injective mirrorWord :=
  Function.Involutive.injective mirrorWord_invol

@[simp] theorem mirrorWord_length (w : List Bool) : (mirrorWord w).length = w.length := by
  simp [mirrorWord]

@[simp] theorem mirror_position (v : Vertex) : (position (mirrorVertex v)).1 = -(position v).1 := by
  cases v <;> simp [mirrorVertex,position] <;> ring

@[simp] theorem mirror_neighbor (v : Vertex) (k : Fin 3) :
    mirrorVertex (neighbor v k) = neighbor (mirrorVertex v) (mirrorSlot k) := by
  cases v <;> fin_cases k <;> simp [mirrorVertex,mirrorSlot,neighbor] <;> omega

@[simp] theorem mirror_advance (g : Germ) (b : Bool) :
    mirrorGerm (advance g b) = advance (mirrorGerm g) (!b) := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    simp [mirrorGerm,mirrorVertex,mirrorSlot,advance,outgoingSlot,neighbor,
      Fin.reduceAdd,Fin.reduceEq,Fin.isValue] <;> omega

@[simp] theorem mirror_terminal (g : Germ) (w : List Bool) :
    terminalGerm (mirrorGerm g) (mirrorWord w) = mirrorGerm (terminalGerm g w) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    simp only [mirrorWord,List.map_cons,terminalGerm,← mirror_advance]
    exact ih _

@[simp] theorem mirror_traced (g : Germ) (w : List Bool) :
    traced (mirrorGerm g) (mirrorWord w) = (traced g w).map mirrorVertex := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    change mirrorVertex g.1 :: traced (advance (mirrorGerm g) (!b)) (mirrorWord w) =
      mirrorVertex g.1 :: (traced (advance g b) w).map mirrorVertex
    rw [← mirror_advance,ih]

@[simp] theorem mirror_bottomSource : mirrorGerm bottomSource = bottomSource := by rfl

noncomputable def mirrorDomain (D : Finset Vertex) : Finset Vertex := D.image mirrorVertex

@[simp] theorem mem_mirrorDomain (D : Finset Vertex) (v : Vertex) :
    v ∈ mirrorDomain D ↔ mirrorVertex v ∈ D := by
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    simpa using hu
  · intro hv
    exact Finset.mem_image.mpr ⟨mirrorVertex v,hv,mirrorVertex_invol v⟩

@[simp] theorem mirrorDomain_invol (D : Finset Vertex) : mirrorDomain (mirrorDomain D) = D := by
  ext v
  simp

@[simp] theorem mirror_indices (v : Vertex) :
    boxIndex (mirrorVertex v) 0 = boxIndex v 0 ∧
    boxIndex (mirrorVertex v) 1 = -boxIndex v 2 ∧
    boxIndex (mirrorVertex v) 2 = -boxIndex v 1 := by
  cases v <;> simp [mirrorVertex,boxIndex] <;> omega

theorem mirrorDomain_convex (D : Finset Vertex) (hD : AdmissiblyConvex D) :
    AdmissiblyConvex (mirrorDomain D) := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  let lo' : Fin 3 → ℤ := fun k => if k = 0 then lo 0 else if k = 1 then 1-hi 2 else 1-hi 1
  let hi' : Fin 3 → ℤ := fun k => if k = 0 then hi 0 else if k = 1 then 1-lo 2 else 1-lo 1
  apply admissiblyConvex_of_box _ lo' hi'
  intro v
  rw [mem_mirrorDomain,hbox]
  have hm := mirror_indices v
  constructor
  · intro hv k
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    rw [hm.1] at h0
    rw [hm.2.1] at h1
    rw [hm.2.2] at h2
    fin_cases k <;> simp [lo',hi'] <;> omega
  · intro hv k
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    simp only [lo',hi',Fin.isValue,Fin.reduceEq,ite_true,ite_false] at h0 h1 h2
    fin_cases k
    · change lo 0 ≤ boxIndex (mirrorVertex v) 0 ∧ boxIndex (mirrorVertex v) 0 < hi 0
      rw [hm.1]; omega
    · change lo 1 ≤ boxIndex (mirrorVertex v) 1 ∧ boxIndex (mirrorVertex v) 1 < hi 1
      rw [hm.2.1]; omega
    · change lo 2 ≤ boxIndex (mirrorVertex v) 2 ∧ boxIndex (mirrorVertex v) 2 < hi 2
      rw [hm.2.2]; omega

theorem mirrorDomain_strip (h : ℕ) (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v) :
    ∀ v ∈ mirrorDomain D, InStrip h v := by
  intro v hv
  have hh := hstrip _ ((mem_mirrorDomain D v).mp hv)
  simpa only [InStrip,(mirror_indices v).1] using hh

theorem mirror_sourceExits (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : w ∈ sourceExits D g) : mirrorWord w ∈ sourceExits (mirrorDomain D) (mirrorGerm g) := by
  obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
  obtain ⟨hn,hm⟩ := stopped_traced D g w hs
  have ht' : (terminalGerm (mirrorGerm g) (mirrorWord w)).1 ∉ mirrorDomain D := by
    rw [mirror_terminal]
    change mirrorVertex (terminalGerm g w).1 ∉ mirrorDomain D
    rwa [mem_mirrorDomain,mirrorVertex_invol]
  apply (mem_sourceExits _ _ _).mpr
  refine ⟨stopped_of_trace _ _ _ ?_ ?_ ht',ht'⟩
  · rw [mirror_traced]
    exact hn.map mirrorVertex_injective
  · intro v hv
    rw [mirror_traced,List.mem_map] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    simpa only [mem_mirrorDomain,mirrorVertex_invol] using hm u hu

theorem mirror_sourceExits_eq (D : Finset Vertex) :
    sourceExits (mirrorDomain D) bottomSource = (sourceExits D bottomSource).image mirrorWord := by
  ext w
  constructor
  · intro hw
    refine Finset.mem_image.mpr ⟨mirrorWord w,?_,mirrorWord_invol w⟩
    simpa only [mirrorDomain_invol,mirror_bottomSource] using
      mirror_sourceExits (mirrorDomain D) bottomSource w hw
  · intro hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
    simpa only [mirror_bottomSource] using mirror_sourceExits D bottomSource u hu

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def reachesRight (t : ℝ) (w : List Bool) : Prop :=
  ∃ v ∈ traced bottomSource w, t ≤ (position v).1

noncomputable def rightDistanceMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact positiveWordMass ((sourceExits D bottomSource).filter (reachesRight t))

noncomputable def tailRate : ℝ := -Real.log rayContraction / 2
noncomputable def tailConstant : ℝ :=
  2 * (Real.cos (3*Real.pi/8))⁻¹ * Real.exp (-Real.log rayContraction)

theorem tailRate_pos : 0 < tailRate := by
  have h := Real.log_neg rayContraction_range.1 rayContraction_range.2
  exact div_pos (neg_pos.mpr h) (by norm_num)

theorem tailConstant_pos : 0 < tailConstant := by
  have hc : 0 < Real.cos (3*Real.pi/8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr hc)) (Real.exp_pos _)

theorem rightDistanceMass_mono (D : Finset Vertex) (s t : ℝ) (hst : s ≤ t) :
    rightDistanceMass D t ≤ rightDistanceMass D s := by
  classical
  apply positiveWordMass_mono
  intro w hw
  obtain ⟨he,v,hv,ht⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨he,v,hv,hst.trans ht⟩

theorem rightDistanceMass_geometric (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (n : ℕ) :
    rightDistanceMass D (2 * n * (h+1)) ≤
      (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero,mul_zero,zero_mul,pow_zero,mul_one]
    apply (positiveWordMass_mono (Finset.filter_subset _ _)).trans
    exact boundary_source_weight_bound D bottomSource hD hg (bottomSource_outside_of_strip h D hstrip)
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    apply le_trans (positiveWordMass_mono ?_) (rightIndexMass_geometric h hh D hD hg hstrip n)
    intro w hw
    obtain ⟨he,v,hv,ht⟩ := Finset.mem_filter.mp hw
    have hvm := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := (strip_index_bounds h v (hstrip v hvm)).2
    have hi' : (boxIndex v 2 : ℝ) ≤ (boxIndex v 1 : ℝ) + h := by exact_mod_cast hi
    have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    have hbound : (n : ℝ)*h ≤ (boxIndex v 1 : ℝ) := by
      rw [position_index] at ht
      nlinarith
    exact (mem_lost_upperCut D bottomSource 1 ((n : ℤ)*h) w).mpr
      ⟨he,v,hv,by exact_mod_cast hbound⟩

theorem rightDistanceMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    rightDistanceMass D t ≤ tailConstant / 2 * Real.exp (-tailRate*t/(h+1)) := by
  let n : ℕ := ⌊t / (2 * (h+1 : ℝ))⌋₊
  have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
  have hd : (0 : ℝ) < 2*((h : ℝ)+1) := by positivity
  have hnlo : (n : ℝ) ≤ t/(2*(h+1)) := Nat.floor_le (div_nonneg ht hd.le)
  have hnhi : t/(2*(h+1)) < (n : ℝ)+1 := Nat.lt_floor_add_one _
  have hthreshold : 2*(n : ℝ)*(h+1) ≤ t := by
    have := (le_div_iff₀ hd).mp hnlo
    nlinarith
  have hgeo := (rightDistanceMass_mono D _ _ hthreshold).trans
    (rightDistanceMass_geometric h hh D hD hg hstrip n)
  have hlog := Real.log_neg rayContraction_range.1 rayContraction_range.2
  have he : (n : ℝ)*Real.log rayContraction ≤
      -Real.log rayContraction + -tailRate*t/(h+1) := by
    have hm := mul_le_mul_of_nonpos_right (le_of_lt hnhi) hlog.le
    have heq : -tailRate*t/(h+1) =
        t/(2*(h+1))*Real.log rayContraction := by
      dsimp [tailRate]
      field_simp
    rw [heq]
    nlinarith [hm]
  have hp : rayContraction ^ n ≤
      Real.exp (-Real.log rayContraction) * Real.exp (-tailRate*t/(h+1)) := by
    rw [← Real.exp_add]
    conv_lhs => rw [← Real.exp_log rayContraction_range.1,← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr he
  have hc : 0 ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
    apply inv_nonneg.mpr
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]
  calc
    _ ≤ (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := hgeo
    _ ≤ (Real.cos (3*Real.pi/8))⁻¹ *
        (Real.exp (-Real.log rayContraction) * Real.exp (-tailRate*t/(h+1))) :=
      mul_le_mul_of_nonneg_left hp hc
    _ = _ := by dsimp [tailConstant]; ring

@[simp] theorem reachesRight_mirror (t : ℝ) (w : List Bool) :
    reachesRight t (mirrorWord w) ↔ ∃ v ∈ traced bottomSource w, t ≤ -(position v).1 := by
  have hm := mirror_traced bottomSource w
  rw [mirror_bottomSource] at hm
  simp only [reachesRight,hm,List.mem_map]
  constructor
  · rintro ⟨v,⟨u,hu,rfl⟩,ht⟩
    exact ⟨u,hu,by simpa using ht⟩
  · rintro ⟨v,hv,ht⟩
    exact ⟨mirrorVertex v,⟨v,hv,rfl⟩,by simpa using ht⟩

theorem lateralMass_le_sides (D : Finset Vertex) (t : ℝ) :
    lateralMass D t ≤ rightDistanceMass D t + rightDistanceMass (mirrorDomain D) t := by
  classical
  simp only [rightDistanceMass,positiveWordMass,Finset.sum_filter,mirror_sourceExits_eq]
  rw [Finset.sum_image (fun a _ b _ hab => mirrorWord_injective hab),← Finset.sum_add_distrib]
  unfold lateralMass
  apply Finset.sum_le_sum
  intro w hw
  simp only [mirrorWord_length]
  by_cases hr : reachesRight t w
  · simp only [hr,ite_true]
    split_ifs <;> nlinarith [pow_nonneg criticalActivity_pos.le w.length]
  · by_cases hl : reachesRight t (mirrorWord w)
    · simp only [hr,hl,ite_false,ite_true,zero_add]
      split_ifs <;> first | exact le_rfl | exact pow_nonneg criticalActivity_pos.le _
    · have hnone : ¬ reachesDistance t w := by
        rintro ⟨v,hv,hv'⟩
        have hab := le_abs.mp hv'
        rcases hab with h | h
        · exact hr ⟨v,hv,h⟩
        · exact hl ((reachesRight_mirror t w).mpr ⟨v,hv,h⟩)
      simp only [hr,hl,hnone,ite_false,zero_add,le_refl]

theorem lateralMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    lateralMass D t ≤ tailConstant * Real.exp (-tailRate*t/(h+1)) := by
  have h1 := rightDistanceMass_exp h hh D hD hg hstrip t ht
  have h2 := rightDistanceMass_exp h hh (mirrorDomain D) (mirrorDomain_convex D hD)
    (by simpa only [mem_mirrorDomain,show mirrorVertex bottomSource.1 = bottomSource.1 from rfl] using hg)
    (mirrorDomain_strip h D hstrip) t ht
  have hs := lateralMass_le_sides D t
  linarith

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def vertexWindow (h M : ℕ) : Finset Vertex :=
  ((Finset.Icc (-(M : ℤ)) M).product (Finset.Ico (0 : ℤ) h)).biUnion
    fun p => {Vertex.up p.1 p.2,Vertex.down p.1 p.2}

theorem mem_vertexWindow (h M : ℕ) (v : Vertex) : v ∈ vertexWindow h M ↔
    -(M : ℤ) ≤ boxIndex v 1 ∧ boxIndex v 1 ≤ M ∧ InStrip h v := by
  cases v <;>
    simp [vertexWindow,Finset.mem_biUnion,Finset.mem_Icc,
      Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton,InStrip,boxIndex,
      Vertex.up.injEq,Vertex.down.injEq] <;> aesop

theorem vertexWindow_card_le (h M : ℕ) : (vertexWindow h M).card ≤ 2*(2*M+1)*h := by
  have hc := Finset.card_biUnion_le (s := (Finset.Icc (-(M : ℤ)) M).product (Finset.Ico (0 : ℤ) h))
    (t := fun p => {Vertex.up p.1 p.2,Vertex.down p.1 p.2})
  change (vertexWindow h M).card ≤ _ at hc
  have hs : (∑ p ∈ (Finset.Icc (-(M : ℤ)) M).product (Finset.Ico (0 : ℤ) h),
      ({Vertex.up p.1 p.2,Vertex.down p.1 p.2} : Finset Vertex).card) = 2*(2*M+1)*h := by
    have hcast : ((M : ℤ) + 1 + M).toNat = 2*M+1 := by omega
    simp [Finset.card_product,Int.card_Icc,Int.card_Ico,hcast]
    ring
  exact hc.trans_eq hs

theorem bounded_position_mem_window (h n : ℕ) (v : Vertex) (hv : InStrip h v)
    (hx : |(position v).1| < 2*((n : ℝ)+1)*(h+1)) :
    v ∈ vertexWindow h ((2*(n+1)+1)*(h+1)) := by
  have hi := strip_index_bounds h v hv
  have hi0 : (boxIndex v 1 : ℝ) ≤ (boxIndex v 2 : ℝ) := by exact_mod_cast hi.1
  have hi1 : (boxIndex v 2 : ℝ) ≤ (boxIndex v 1 : ℝ) + h := by exact_mod_cast hi.2
  have hab := abs_lt.mp hx
  rw [position_index] at hab
  apply (mem_vertexWindow _ _ _).mpr
  refine ⟨?_,?_,hv⟩
  · have : -(((2*(n+1)+1)*(h+1) : ℕ) : ℝ) ≤ (boxIndex v 1 : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) h]
    exact_mod_cast this
  · have : (boxIndex v 1 : ℝ) ≤ (((2*(n+1)+1)*(h+1) : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) h]
    exact_mod_cast this

theorem strip_shell_card_le (h n : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) (S : Finset Vertex) (hSD : S ⊆ D)
    (hS : ∀ v ∈ S, |(position v).1| < 2*((n : ℝ)+1)*(h+1)) :
    (S.card : ℝ) ≤ 20*((n : ℝ)+1)*((h : ℝ)+1)^2 := by
  have hsub : S ⊆ vertexWindow h ((2*(n+1)+1)*(h+1)) := by
    intro v hv
    exact bounded_position_mem_window h n v (hstrip v (hSD hv)) (hS v hv)
  have hc := (Finset.card_le_card hsub).trans (vertexWindow_card_le h _)
  have hc' : (S.card : ℝ) ≤ (2*(2*((2*(n+1)+1)*(h+1))+1)*h : ℕ) := by exact_mod_cast hc
  push_cast at hc'
  nlinarith [Nat.cast_nonneg (α := ℝ) h,Nat.cast_nonneg (α := ℝ) n,
    sq_nonneg ((h : ℝ)+1),mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (h : ℝ))]



theorem vertexWindow_convex (h M : ℕ) : AdmissiblyConvex (vertexWindow h M) := by
  apply admissiblyConvex_of_box _
    (fun k => if k = 0 then 0 else -(M : ℤ))
    (fun k => if k = 0 then h else if k = 1 then M+1 else M+h+1)
  intro v
  rw [mem_vertexWindow]
  constructor
  · rintro ⟨hlo,hhi,hstrip⟩ k
    have hb := strip_index_bounds h v hstrip
    fin_cases k <;> simp only [Fin.zero_eta,ite_true,Fin.reduceEq,ite_false]
    · exact hstrip
    · change -(M : ℤ) ≤ boxIndex v 1 ∧ boxIndex v 1 < (M : ℤ)+1
      omega
    · change -(M : ℤ) ≤ boxIndex v 2 ∧ boxIndex v 2 < (M : ℤ)+h+1
      omega
  · intro hv
    have h0 := hv 0
    have h1 := hv 1
    simp only [Fin.reduceEq,ite_false,ite_true] at h0 h1
    exact ⟨h1.1,by omega,h0⟩

theorem bottomSource_mem_window (h M : ℕ) (hh : 1 ≤ h) :
    bottomSource.1 ∈ vertexWindow h M := by
  rw [mem_vertexWindow]
  simp only [bottomSource,boxIndex,Fin.reduceEq,ite_false,ite_true,InStrip]
  omega

theorem vertexWindow_strip (h M : ℕ) : ∀ v ∈ vertexWindow h M, InStrip h v := by
  intro v hv
  exact ((mem_vertexWindow _ _ _).mp hv).2.2

theorem finite_vertices_in_window (h : ℕ) (S : Finset Vertex)
    (hs : ∀ v ∈ S, InStrip h v) : ∃ M : ℕ, S ⊆ vertexWindow h M := by
  let M := S.sup (fun v => (boxIndex v 1).natAbs)
  refine ⟨M,?_⟩
  intro v hv
  have ha : (boxIndex v 1).natAbs ≤ M := Finset.le_sup (f := fun v => (boxIndex v 1).natAbs) hv
  have ha' : (|(boxIndex v 1)| : ℤ) ≤ (M : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast ha
  have hab := abs_le.mp ha'
  exact (mem_vertexWindow _ _ _).mpr ⟨hab.1,hab.2,hs v hv⟩

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def shellRatio : ℝ := Real.exp (-tailRate)
noncomputable def spatialConstant : ℝ :=
  20 * (1 + ∑' n : ℕ, ((n : ℝ)+1)*shellRatio^n)

 theorem shellRatio_range : 0 < shellRatio ∧ shellRatio < 1 := by
  constructor
  · exact Real.exp_pos _
  · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos tailRate_pos)

theorem shellSeries_summable : Summable (fun n : ℕ => ((n : ℝ)+1)*shellRatio^n) := by
  have hn : ‖shellRatio‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos shellRatio_range.1]
    exact shellRatio_range.2
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h0 := summable_geometric_of_norm_lt_one hn
  simpa only [pow_one,add_mul,one_mul] using h1.add h0

theorem spatialConstant_pos : 0 < spatialConstant := by
  have h : 0 ≤ ∑' n : ℕ, ((n : ℝ)+1)*shellRatio^n :=
    tsum_nonneg (fun n => mul_nonneg (by positivity) (pow_nonneg shellRatio_range.1.le _))
  dsimp [spatialConstant]
  linarith

noncomputable def shellIndex (h : ℕ) (v : Vertex) : ℕ :=
  ⌊|(position v).1|/(2*((h : ℝ)+1))⌋₊

theorem shellIndex_bounds (h : ℕ) (v : Vertex) :
    (shellIndex h v : ℝ) ≤ |(position v).1|/(2*((h : ℝ)+1)) ∧
    |(position v).1| < 2*((shellIndex h v : ℝ)+1)*((h : ℝ)+1) := by
  have hd : (0 : ℝ) < 2*((h : ℝ)+1) := by positivity
  refine ⟨Nat.floor_le (div_nonneg (abs_nonneg _) hd.le),?_⟩
  have hh := Nat.lt_floor_add_one (|(position v).1|/(2*((h : ℝ)+1)))
  have hi := (div_lt_iff₀ hd).mp hh
  dsimp [shellIndex]
  nlinarith

theorem spatial_sum_exp_bound (h : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) :
    (∑ v ∈ D, Real.exp (-tailRate*|(position v).1|/(2*(h+1)))) ≤
      spatialConstant*((h : ℝ)+1)^2 := by
  classical
  let S := D.image (shellIndex h)
  have hsplit := Finset.sum_fiberwise_of_maps_to
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩ : ∀ v ∈ D, shellIndex h v ∈ S)
    (fun v => Real.exp (-tailRate*|(position v).1|/(2*(h+1))))
  rw [← hsplit]
  have hs : ∀ n ∈ S,
      (∑ v ∈ D with shellIndex h v = n,
        Real.exp (-tailRate*|(position v).1|/(2*(h+1)))) ≤
      20*((n : ℝ)+1)*((h : ℝ)+1)^2 * shellRatio^n := by
    intro n hn
    have hc := strip_shell_card_le h n D hstrip (D.filter (fun v => shellIndex h v = n))
      (Finset.filter_subset _ _) (by
        intro v hv
        obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
        simpa only [he] using (shellIndex_bounds h v).2)
    calc
      _ ≤ ∑ v ∈ D with shellIndex h v = n, shellRatio^n := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
        rw [shellRatio,← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hl := (shellIndex_bounds h v).1
        rw [he] at hl
        have hm := mul_le_mul_of_nonpos_left hl (neg_nonpos.mpr tailRate_pos.le)
        calc
          -tailRate*|(position v).1|/(2*(h+1)) =
              -tailRate*(|(position v).1|/(2*(h+1))) := by ring
          _ ≤ -tailRate*(n : ℝ) := hm
          _ = (n : ℝ)*-tailRate := by ring
      _ = ((D.filter (fun v => shellIndex h v = n)).card : ℝ) * shellRatio^n := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (pow_nonneg shellRatio_range.1.le _)
  calc
    _ ≤ ∑ n ∈ S, 20*((n : ℝ)+1)*((h : ℝ)+1)^2 * shellRatio^n :=
      Finset.sum_le_sum hs
    _ = 20*((h : ℝ)+1)^2 * ∑ n ∈ S, ((n : ℝ)+1)*shellRatio^n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 20*((h : ℝ)+1)^2 * (∑' n : ℕ, ((n : ℝ)+1)*shellRatio^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact shellSeries_summable.sum_le_tsum S
        (fun n _ => mul_nonneg (by positivity) (pow_nonneg shellRatio_range.1.le _))
    _ ≤ spatialConstant*((h : ℝ)+1)^2 := by
      dsimp [spatialConstant]
      nlinarith [sq_nonneg ((h : ℝ)+1)]

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def eventVisitMass (D : Finset Vertex) (t : ℝ) (v : Vertex) : ℝ := by
  classical
  exact ∑ w ∈ sourceExits D bottomSource,
    if reachesDistance t w ∧ v ∈ traced bottomSource w then criticalActivity^w.length else 0

theorem sourceExit_visit_sum (D : Finset Vertex) (w : List Bool)
    (hw : w ∈ sourceExits D bottomSource) :
    (∑ v ∈ D, if v ∈ traced bottomSource w then criticalActivity^w.length else 0) =
      (w.length : ℝ)*criticalActivity^w.length := by
  classical
  have hs := stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp hw).1
  have hset : D.filter (fun v => v ∈ traced bottomSource w) = (traced bottomSource w).toFinset := by
    ext v
    simp only [Finset.mem_filter,List.mem_toFinset]
    exact ⟨And.right,fun hv => ⟨hs.2 v hv,hv⟩⟩
  rw [← Finset.sum_filter,hset]
  simp only [Finset.sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup hs.1,traced_length]

theorem lateralLengthMass_fubini (D : Finset Vertex) (t : ℝ) :
    lateralLengthMass D t = ∑ v ∈ D, eventVisitMass D t v := by
  classical
  unfold eventVisitMass
  rw [Finset.sum_comm]
  unfold lateralLengthMass
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ht : reachesDistance t w
  · simp only [ht,true_and,ite_true]
    exact (sourceExit_visit_sum D w hw).symm
  · simp only [ht,false_and,ite_false,Finset.sum_const_zero]

theorem eventVisitMass_le_lateral (D : Finset Vertex) (t : ℝ) (v : Vertex) :
    eventVisitMass D t v ≤ lateralMass D (max t |(position v).1|) := by
  classical
  unfold eventVisitMass lateralMass
  apply Finset.sum_le_sum
  intro w hw
  by_cases he : reachesDistance t w ∧ v ∈ traced bottomSource w
  · have hm : reachesDistance (max t |(position v).1|) w := by
      rcases le_total t |(position v).1| with h | h
      · exact ⟨v,he.2,by rw [max_eq_right h]⟩
      · rw [max_eq_left h]
        exact he.1
    simp [he,hm]
  · simp only [he,ite_false]
    split_ifs <;> first | exact le_rfl | exact pow_nonneg criticalActivity_pos.le _

theorem eventVisitMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) (v : Vertex) :
    eventVisitMass D t v ≤ tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
      Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by
  have hm := lateralMass_exp h hh D hD hg hstrip (max t |(position v).1|)
    (ht.trans (le_max_left _ _))
  have he : Real.exp (-tailRate*max t |(position v).1|/(h+1)) ≤
      Real.exp (-tailRate*t/(2*(h+1))) *
      Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha := le_max_left t |(position v).1|
    have hb := le_max_right t |(position v).1|
    have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
    have hf : -tailRate*max t |(position v).1| ≤
        -tailRate*(t + |(position v).1|)/2 := by
      nlinarith [mul_nonneg tailRate_pos.le (show 0 ≤ 2*max t |(position v).1| - t - |(position v).1| by linarith)]
    have hd := div_le_div_of_nonneg_right hf hH.le
    have heq : -tailRate*t/(2*(h+1)) + -tailRate*|(position v).1|/(2*(h+1)) =
        (-tailRate*(t + |(position v).1|)/2)/(h+1) := by
      field_simp
      ring
    rw [heq]
    exact hd
  calc
    _ ≤ lateralMass D (max t |(position v).1|) := eventVisitMass_le_lateral D t v
    _ ≤ tailConstant * Real.exp (-tailRate*max t |(position v).1|/(h+1)) := hm
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he tailConstant_pos.le

theorem lateralLengthMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    lateralLengthMass D t ≤ tailConstant*spatialConstant*((h : ℝ)+1)^2 *
      Real.exp (-(tailRate/2)*t/(h+1)) := by
  rw [lateralLengthMass_fubini]
  calc
    _ ≤ ∑ v ∈ D, tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        Real.exp (-tailRate*|(position v).1|/(2*(h+1))) :=
      Finset.sum_le_sum (fun v _ => eventVisitMass_exp h hh D hD hg hstrip t ht v)
    _ = tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        ∑ v ∈ D, Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by rw [Finset.mul_sum]
    _ ≤ tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        (spatialConstant*((h : ℝ)+1)^2) :=
      mul_le_mul_of_nonneg_left (spatial_sum_exp_bound h D hstrip)
        (mul_nonneg tailConstant_pos.le (Real.exp_pos _).le)
    _ = _ := by
      have he : -tailRate*t/(2*(h+1)) = -(tailRate/2)*t/(h+1) := by
        field_simp
      rw [he]
      ring



theorem finite_lateral_tail : FiniteLateralTail := by
  let C := tailConstant*(1+spatialConstant)
  have hCp : 0 < C := mul_pos tailConstant_pos (by linarith [spatialConstant_pos])
  have hC : tailConstant ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg tailConstant_pos.le spatialConstant_pos.le]
  have hC' : tailConstant*spatialConstant ≤ C := by
    dsimp [C]
    linarith [tailConstant_pos]
  refine ⟨C,tailRate/2,hCp,div_pos tailRate_pos (by norm_num),?_⟩
  intro h D hh hD hg hstrip t ht
  have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
  constructor
  · have he : Real.exp (-tailRate*t/(h+1)) ≤ Real.exp (-(tailRate/2)*t/(h+1)) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hH.le
      nlinarith [mul_nonneg tailRate_pos.le ht]
    exact (lateralMass_exp h hh D hD hg hstrip t ht).trans
      (mul_le_mul hC he (Real.exp_pos _).le hCp.le)
  · apply (lateralLengthMass_exp h hh D hD hg hstrip t ht).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hhh : ((h : ℝ)+1)^2 ≤ ((h : ℝ)+1)*(h+t+1) := by
      nlinarith [mul_nonneg hH.le ht]
    calc
      _ ≤ C*((h : ℝ)+1)^2 := mul_le_mul_of_nonneg_right hC' (sq_nonneg _)
      _ ≤ C*(((h : ℝ)+1)*(h+t+1)) := mul_le_mul_of_nonneg_left hhh hCp.le
      _ = _ := by ring

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

 theorem adjacent_exists_slot (v u : Vertex) (h : adjacent v u) :
    ∃ k : Fin 3, neighbor v k = u := by
  cases v <;> cases u <;> simp only [adjacent] at h
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨0,by simp [neighbor]⟩
    · exact ⟨1,by simp [neighbor]⟩
    · exact ⟨2,by simp [neighbor]⟩
  · rcases h with ⟨rfl,hl⟩ | ⟨rfl,rfl⟩ | ⟨hk,rfl⟩
    · exact ⟨0,by simp [neighbor]; omega⟩
    · exact ⟨1,by simp [neighbor]⟩
    · exact ⟨2,by simp [neighbor]; omega⟩

theorem exists_advance_of_adjacent (g : Germ) (v : Vertex) (ha : adjacent g.1 v)
    (hb : v ≠ neighbor g.1 g.2) : ∃ b : Bool, (advance g b).1 = v := by
  obtain ⟨k,hk⟩ := adjacent_exists_slot g.1 v ha
  have hkg : k ≠ g.2 := by
    intro he
    exact hb (he ▸ hk.symm)
  have ho : ∃ b : Bool, outgoingSlot g b = k := by
    obtain ⟨u,j⟩ := g
    fin_cases j <;> fin_cases k <;> simp_all [outgoingSlot]
  obtain ⟨b,hb⟩ := ho
  exact ⟨b,by simpa only [advance,hb] using hk⟩

theorem exists_word_of_chain (g : Germ) (l : List Vertex)
    (hc : (g.1 :: l).IsChain adjacent) (hn : (g.1 :: l).Nodup)
    (hp : neighbor g.1 g.2 ∉ l) :
    ∃ w : List Bool, traced g w ++ [(terminalGerm g w).1] = g.1 :: l := by
  induction l generalizing g with
  | nil => exact ⟨[],rfl⟩
  | cons v l ih =>
    obtain ⟨ha,hc⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨hg,hn⟩ := List.nodup_cons.mp hn
    have hb : v ≠ neighbor g.1 g.2 := by
      intro he
      exact hp (by simp [he])
    obtain ⟨b,hb⟩ := exists_advance_of_adjacent g v ha hb
    have hg' : neighbor (advance g b).1 (advance g b).2 = g.1 := by
      simp only [advance,neighbor_neighbor]
    have hc' : ((advance g b).1 :: l).IsChain adjacent := by simpa only [hb] using hc
    have hn' : ((advance g b).1 :: l).Nodup := by simpa only [hb] using hn
    have hp' : neighbor (advance g b).1 (advance g b).2 ∉ l := by
      rw [hg']
      exact fun hm => hg (List.mem_cons_of_mem _ hm)
    obtain ⟨w,hw⟩ := ih (advance g b) hc' hn' hp'
    refine ⟨b::w,?_⟩
    simp only [traced,terminalGerm,List.cons_append,hw,hb]
noncomputable def bridgeLengthMass (h : ℕ) : ℝ :=
  ∑' p : BridgePath h, firstLengthWeight p
noncomputable def bridgeMean (h : ℕ) : ℝ := bridgeLengthMass h / bridgeMass h
noncomputable def confinedLengthMass (h : ℕ) : ℝ :=
  ∑' p : ConfinedBridgePath h, firstLengthWeight p.val
noncomputable def confinedMean (h : ℕ) : ℝ := confinedLengthMass h / confinedMass h

def Subpower (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (∀ᶠ h in Filter.atTop, 0 < f h) ∧
  Filter.Tendsto (fun h : ℕ => Real.log (f h) / Real.log (h : ℝ))
    Filter.atTop (nhds a)

def StripMassAndBridgeLength : Prop :=
  FiniteBridgeSums ∧
  Subpower bridgeMass (-(1 : ℝ) / 4) ∧
  Subpower bridgeLengthMass ((13 : ℝ) / 12) ∧
  Subpower bridgeMean ((4 : ℝ) / 3) ∧
  Subpower confinedMass (-(1 : ℝ) / 4) ∧
  Subpower confinedLengthMass ((13 : ℝ) / 12) ∧
  Subpower confinedMean ((4 : ℝ) / 3)



@[simp] theorem layer_boxIndex (v : Vertex) : layer v = boxIndex v 0 := by
  cases v <;> simp [layer,boxIndex]

theorem bridge_exists_word (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    ∃ w : List Bool, traced bottomSource w = p.vertices ∧
      layer (terminalGerm bottomSource w).1 = (h : ℤ) := by
  obtain ⟨i,hi⟩ := p.terminal
  let u : Vertex := .up i h
  have hu : layer u = (h : ℤ) := by rfl
  have hnu : u ∉ p.vertices := by
    intro hm
    have h := (p.inStrip u hm).2
    rw [hu] at h
    omega
  have hc : (p.vertices ++ [u]).IsChain adjacent := by
    apply p.connected.append (by simp)
    intro v hv a ha
    have hv' : v = .down i ((h : ℤ)-1) := by symm; simpa only [hi,Option.mem_some_iff] using hv
    have ha' : a = u := by symm; simpa using ha
    subst v; subst a
    simp [u,adjacent]
  have hn : (p.vertices ++ [u]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨p.distinct,by simp,?_⟩
    intro v hv a ha
    have ha' : a = u := by simpa using ha
    subst a
    exact fun he => hnu (he ▸ hv)
  have hp : neighbor bottomSource.1 bottomSource.2 ∉ p.vertices ++ [u] := by
    intro hm
    simp only [List.mem_append,List.mem_singleton] at hm
    rcases hm with hm | hm
    · have hi := (p.inStrip _ hm).1
      norm_num [bottomSource,neighbor,layer,boxIndex] at hi
    · have hidx := congrArg layer hm
      change (-1 : ℤ) = (h : ℤ) at hidx
      have hheight : (1 : ℤ) ≤ h := by exact_mod_cast hh
      exact (ne_of_lt (lt_of_lt_of_le (by norm_num : (-1 : ℤ) < 1) hheight)) hidx
  obtain ⟨l,hl⟩ := List.head?_eq_some_iff.mp p.source
  have hc' : (bottomSource.1 :: (l ++ [u])).IsChain adjacent := by
    simpa only [hl,List.cons_append,bottomSource] using hc
  have hn' : (bottomSource.1 :: (l ++ [u])).Nodup := by
    simpa only [hl,List.cons_append,bottomSource] using hn
  have hp' : neighbor bottomSource.1 bottomSource.2 ∉ l ++ [u] := by
    intro hm
    apply hp
    rw [hl,List.cons_append]
    exact List.mem_cons_of_mem _ hm
  obtain ⟨w,hw⟩ := exists_word_of_chain bottomSource _ hc' hn' hp'
  have heq : traced bottomSource w ++ [(terminalGerm bottomSource w).1] = p.vertices ++ [u] := by
    simpa only [hl,List.cons_append,bottomSource] using hw
  have ht : (terminalGerm bottomSource w).1 = u := by
    have ht := congrArg List.getLast? heq
    simpa using ht
  rw [ht] at heq
  exact ⟨w,List.append_cancel_right heq,ht ▸ hu⟩

noncomputable def bridgeWord (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) : List Bool :=
  (bridge_exists_word h hh p).choose

@[simp] theorem bridgeWord_trace (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    traced bottomSource (bridgeWord h hh p) = p.vertices :=
  (bridge_exists_word h hh p).choose_spec.1

theorem bridgeWord_terminal_layer (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    layer (terminalGerm bottomSource (bridgeWord h hh p)).1 = (h : ℤ) :=
  (bridge_exists_word h hh p).choose_spec.2

@[simp] theorem bridgeWord_length (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    (bridgeWord h hh p).length = p.vertices.length := by
  rw [← traced_length bottomSource,bridgeWord_trace]

theorem bridgeWord_injective (h : ℕ) (hh : 1 ≤ h) : Function.Injective (bridgeWord h hh) := by
  intro p q hpq
  have hv := congrArg (traced bottomSource) hpq
  simp only [bridgeWord_trace] at hv
  cases p; cases q
  cases hv
  rfl

theorem bridgeWord_mem_sourceExits (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h)
    (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v)
    (hp : ∀ v ∈ p.vertices, v ∈ D) : bridgeWord h hh p ∈ sourceExits D bottomSource := by
  have ht : (terminalGerm bottomSource (bridgeWord h hh p)).1 ∉ D := by
    intro hm
    have hhi := (hstrip _ hm).2
    rw [← layer_boxIndex,bridgeWord_terminal_layer] at hhi
    omega
  apply (mem_sourceExits _ _ _).mpr
  refine ⟨stopped_of_trace D bottomSource _ ?_ ?_ ht,ht⟩
  · simpa only [bridgeWord_trace] using p.distinct
  · simpa only [bridgeWord_trace] using hp

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem finite_bridges_window (h : ℕ) (S : Finset (BridgePath h)) :
    ∃ M : ℕ, ∀ p ∈ S, ∀ v ∈ p.vertices, v ∈ vertexWindow h M := by
  classical
  let V := S.biUnion (fun p => p.vertices.toFinset)
  have hV : ∀ v ∈ V, InStrip h v := by
    intro v hv
    obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp hv
    have hi := p.inStrip v (List.mem_toFinset.mp hv)
    simpa only [InStrip,layer_boxIndex] using hi
  obtain ⟨M,hM⟩ := finite_vertices_in_window h V hV
  refine ⟨M,?_⟩
  intro p hp v hv
  exact hM (Finset.mem_biUnion.mpr ⟨p,hp,List.mem_toFinset.mpr hv⟩)

theorem bridge_finite_sum_word_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h))
    (f : List Bool → ℝ) (hf : ∀ w, 0 ≤ f w) :
    ∃ M : ℕ, (∑ p ∈ S, f (bridgeWord h hh p)) ≤
      ∑ w ∈ sourceExits (vertexWindow h M) bottomSource, f w := by
  classical
  obtain ⟨M,hM⟩ := finite_bridges_window h S
  refine ⟨M,?_⟩
  rw [← Finset.sum_image (fun p _ q _ he => bridgeWord_injective h hh he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun w _ _ => hf w)
  intro w hw
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
  exact bridgeWord_mem_sourceExits h hh p _ (vertexWindow_strip h M) (hM p hp)

theorem bridge_weight_finite_sum_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h)) :
    (∑ p ∈ S, weight p) ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
  obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S (fun w => criticalActivity^w.length)
    (fun w => pow_nonneg criticalActivity_pos.le _)
  simp only [bridgeWord_length] at hM
  apply hM.trans
  exact boundary_source_weight_bound _ bottomSource (vertexWindow_convex h M)
    (bottomSource_mem_window h M hh)
    (bottomSource_outside_of_strip h _ (vertexWindow_strip h M))

theorem sourceExit_reaches_zero (D : Finset Vertex) (hg : bottomSource.1 ∈ D)
    (w : List Bool) (hw : w ∈ sourceExits D bottomSource) : reachesDistance 0 w := by
  cases w with
  | nil =>
    have hn := ((mem_sourceExits _ _ _).mp hw).1
    exact False.elim (hn hg)
  | cons b w => exact ⟨bottomSource.1,by simp [traced],abs_nonneg _⟩

theorem lateralLengthMass_zero (D : Finset Vertex) (hg : bottomSource.1 ∈ D) :
    lateralLengthMass D 0 = ∑ w ∈ sourceExits D bottomSource,
      (w.length : ℝ)*criticalActivity^w.length := by
  classical
  unfold lateralLengthMass
  apply Finset.sum_congr rfl
  intro w hw
  simp only [sourceExit_reaches_zero D hg w hw,ite_true]

theorem bridge_length_finite_sum_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h)) :
    (∑ p ∈ S, firstLengthWeight p) ≤ tailConstant*spatialConstant*((h : ℝ)+1)^2 := by
  obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S
    (fun w => (w.length : ℝ)*criticalActivity^w.length)
    (fun w => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg criticalActivity_pos.le _))
  simp only [bridgeWord_length] at hM
  rw [← lateralLengthMass_zero _ (bottomSource_mem_window h M hh)] at hM
  apply hM.trans
  have ht := lateralLengthMass_exp h hh _ (vertexWindow_convex h M)
    (bottomSource_mem_window h M hh) (vertexWindow_strip h M) 0 le_rfl
  simpa only [mul_zero,zero_div,Real.exp_zero,mul_one] using ht

theorem bridge_weight_summable (h : ℕ) (hh : 1 ≤ h) : Summable (weight (h := h)) := by
  refine summable_of_sum_le (f := weight (h := h))
    (c := (Real.cos (3*Real.pi/8))⁻¹) ?_ (bridge_weight_finite_sum_bound h hh)
  intro p
  exact pow_nonneg criticalActivity_pos.le p.vertices.length

theorem bridge_length_summable (h : ℕ) (hh : 1 ≤ h) : Summable (firstLengthWeight (h := h)) := by
  refine summable_of_sum_le (f := firstLengthWeight (h := h))
    (c := tailConstant*spatialConstant*((h : ℝ)+1)^2) ?_
    (bridge_length_finite_sum_bound h hh)
  intro p
  exact mul_nonneg (Nat.cast_nonneg p.vertices.length)
    (pow_nonneg criticalActivity_pos.le p.vertices.length)

theorem finite_bridge_sums_oai : FiniteBridgeSums := by
  intro h hh
  have hm := bridge_weight_summable h hh
  have hl := bridge_length_summable h hh
  have hmc : Summable (fun p : ConfinedBridgePath h => weight p.val) := hm.subtype InLogCorridor
  have hlc : Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) := hl.subtype InLogCorridor
  exact ⟨hm,hl,hl.div_const _,hmc,hlc,hlc.div_const _⟩

end PolynomialVacuumBridge.Corridor

end

end OAI
end
end

theorem solution : type_of% @OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_oai := @OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_oai
