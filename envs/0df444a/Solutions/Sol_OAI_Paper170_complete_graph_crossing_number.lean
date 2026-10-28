-- Prove2me | solution 1 for OAI.Paper170.complete_graph_crossing_number
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:42:45.65198+00:00
-- url     : https://prove2.me/submissions/8505dee3-3786-4ce9-acf9-855aff5b09d7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing
import Definitions.Def_OAIQ4Cc002
import Theorems.Thm_OAI_Paper170_complete_graph_lower_bound

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Hill
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harary–Hill arithmetic, residue-page definitions, and the even-order deletion inequality. -/

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem crossing_sum_partial {n m : ℕ} (hn : 3 ≤ n) (hm : 2 * m ≤ n) :
    2 * ∑ k ∈ Finset.Icc 1 m, (k - 1) * (n - k - 1) * (n - 2 * k) =
      m * (m - 1) * (n - m - 1) * (n - m - 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), mul_add,
      ih (by omega)]
    by_cases hzero : m = 0
    · subst m; simp
    have hm₁ : 1 ≤ m := by omega
    zify
    simp (disch := omega) only [Nat.cast_sub, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat]
    ring

theorem crossing_sum_telescope {n : ℕ} (hn : 3 ≤ n) :
    (2 * ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k)) =
      (n / 2) * (n / 2 - 1) * (n - n / 2 - 1) * (n - n / 2 - 2) :=
  crossing_sum_partial hn (by omega)

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem cyclic_count_pairing {n : ℕ} (hn : 3 ≤ n) :
    (∑ k ∈ Finset.Icc 2 (n - 2),
      (k - 1) * (n - k - 1) * (n - 2 * min k (n - k))) =
      2 * ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k) := by
  let F : ℕ → ℕ := fun k => (k - 1) * (n - k - 1) * (n - 2 * min k (n - k))
  have hsym (k : ℕ) (hk : k ≤ n) : F (n - k) = F k := by
    dsimp [F]
    rw [Nat.sub_sub_self hk, min_comm]
    ring
  have hfull : (∑ k ∈ Finset.Icc 2 (n - 2), F k) = ∑ k ∈ Finset.Ico 1 n, F k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk hnot
      simp only [Finset.mem_Ico, Finset.mem_Icc, not_and] at hk hnot
      have he : k = 1 ∨ k = n - 1 := by omega
      rcases he with rfl | rfl
      · simp [F]
      · have he : n - (n - 1) - 1 = 0 := by omega
        simp [F, he]
  have hsplit := Finset.sum_Ico_consecutive F (show 1 ≤ n / 2 + 1 by omega)
    (show n / 2 + 1 ≤ n by omega)
  have htail : (∑ k ∈ Finset.Ico (n / 2 + 1) n, F k) =
      ∑ k ∈ Finset.Ico 1 (n - n / 2), F k := by
    calc
      _ = ∑ k ∈ Finset.Ico (n / 2 + 1) n, F (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hsym k (by have := (Finset.mem_Ico.mp hk).2; omega)).symm
      _ = _ := by
        simpa only [Nat.add_sub_cancel_left, Nat.add_sub_add_right] using
          (Finset.sum_Ico_reflect F (n / 2 + 1) (m := n) (n := n) (by omega))
  have hlow : (∑ k ∈ Finset.Ico 1 (n - n / 2), F k) =
      ∑ k ∈ Finset.Ico 1 (n / 2 + 1), F k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk hnot
      simp only [Finset.mem_Ico, not_and] at hk hnot
      have he : n = 2 * k := by omega
      subst n
      simp [F, show 2 * k - k = k by omega]
  have hterm : (∑ k ∈ Finset.Ico 1 (n / 2 + 1), F k) =
      ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [F]
    rw [min_eq_left (by have := (Finset.mem_Icc.mp hk).2; omega)]
  change (∑ k ∈ Finset.Icc 2 (n - 2), F k) = _
  rw [hfull, ← hsplit, htail, hlow, hterm]
  omega

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Drawing
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous graph drawings, proper spatial crossings, incidence, and endpoint properties. -/

section

/-! Finite point incidence for actual drawings, retaining repeated pair crossings. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
open scoped BigOperators Classical
/-- A minimum exists once an actual admissible drawing has been constructed.
This is the well-ordering step; construction of a drawing remains a separate obligation. -/
theorem crossingCount_attainment (D₀ : Paper170.AdmissibleDrawing graph) :
    ∃ D : Paper170.AdmissibleDrawing graph, Paper170.crossingCount D = Paper170.ordinaryCrossingNumber graph := by
  exact csInf_mem (show (Set.range (@Paper170.crossingCount Vertex Edge graph)).Nonempty from
    ⟨Paper170.crossingCount D₀, D₀, rfl⟩)

theorem ordinaryCrossingNumber_le_count (D : Paper170.AdmissibleDrawing graph) :
    Paper170.ordinaryCrossingNumber graph ≤ Paper170.crossingCount D :=
  csInf_le' ⟨D, rfl⟩

theorem crossing_incident_iff (D : Paper170.AdmissibleDrawing graph) (x : Plane)
    (e f : Edge) (hef : e ≠ f)
    (he : x ∈ Paper170.edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ Paper170.edgeInterior D.toContinuousDrawing f) (g : Edge) :
    x ∈ Paper170.edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  constructor
  · intro hg
    by_contra hh
    have hge : e ≠ g := by tauto
    have hgf : f ≠ g := by tauto
    have hmem : x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∩ Paper170.edgeInterior D.toContinuousDrawing f ∩
        Paper170.edgeInterior D.toContinuousDrawing g := ⟨⟨he,hf⟩,hg⟩
    rw [D.no_triples e f g hef hge hgf] at hmem
    exact hmem
  · rintro (rfl | rfl) <;> assumption

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem circle_denominator_pos (t : ℝ) : 0 < 1+t^2 := by nlinarith [sq_nonneg t]

theorem circlePoint_on_unit_circle (t : ℝ) : (circlePoint t).1^2+(circlePoint t).2^2 = 1 := by
  have h := ne_of_gt (circle_denominator_pos t)
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_parameter (t : ℝ) : (circlePoint t).2/(1+(circlePoint t).1) = t := by
  have h := ne_of_gt (circle_denominator_pos t)
  have hden : 1+(circlePoint t).1 = 2/(1+t^2) := by
    dsimp [circlePoint]
    field_simp
    ring
  rw [hden]
  dsimp [circlePoint]
  field_simp

theorem circlePoint_injective : Function.Injective circlePoint := by
  intro a b hab
  have hh := congrArg (fun z : Plane => z.2/(1+z.1)) hab
  simpa only [circlePoint_parameter] using hh

theorem circle_orient_formula (a b c : ℝ) :
    orient2 (circlePoint a) (circlePoint b) (circlePoint c) =
      4*(b-a)*(c-a)*(c-b)/((1+a^2)*(1+b^2)*(1+c^2)) := by
  have ha := ne_of_gt (circle_denominator_pos a)
  have hb := ne_of_gt (circle_denominator_pos b)
  have hc := ne_of_gt (circle_denominator_pos c)
  dsimp [orient2,det2,circlePoint]
  field_simp
  ring

theorem circle_orient_pos (a b c : ℝ) (hab : a<b) (hbc : b < c) :
    0 < orient2 (circlePoint a) (circlePoint b) (circlePoint c) := by
  rw [circle_orient_formula]
  exact div_pos
    (mul_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hab))
      (sub_pos.mpr (hab.trans hbc))) (sub_pos.mpr hbc))
    (mul_pos (mul_pos (circle_denominator_pos a) (circle_denominator_pos b)) (circle_denominator_pos c))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CircleArcs
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle segments, inversion, continuous paths, and admissibility of two-page arcs. -/

section

noncomputable section
open Set
namespace Paper170

theorem twoPage_edgeInterior {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e : CompleteEdge n) :
    edgeInterior D.toContinuousDrawing e =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e := by
  change (D.edge e : unitInterval → Plane) '' _ = _
  rw [show (D.edge e : unitInterval → Plane) = twoPageRoute C e from funext (hD.edge_eq e)]
  exact twoPageRoute_image C e

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem two_page_drawing_exists {n : ℕ} (C : CircleConfiguration n) :
    ∃ D : AdmissibleDrawing (completeGraph n), TwoPageDrawing C D :=
  ⟨twoPageAdmissible C, rfl, fun _ _ => rfl⟩

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GenericPolynomialBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem exists_box_avoiding_polynomials {σ κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial σ ℝ) (hP : ∀ k, P k ≠ 0)
    (lo hi : σ → ℝ) (hinterval : ∀ i, lo i < hi i) :
    ∃ x : σ → ℝ, (∀ i, x i ∈ Set.Ioo (lo i) (hi i)) ∧ ∀ k, MvPolynomial.eval x (P k) ≠ 0 := by
  classical
  let Q := ∏ k, P k
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hP k)
  have hex : ∃ x : σ → ℝ, (∀ i, x i ∈ Set.Ioo (lo i) (hi i)) ∧ MvPolynomial.eval x Q ≠ 0 := by
    by_contra hh
    apply hQ
    apply MvPolynomial.funext_set (fun i => Set.Ioo (lo i) (hi i)) (fun i => Set.Ioo_infinite (hinterval i))
    intro x hx
    rw [map_zero]
    by_contra hz
    exact hh ⟨x,fun i => hx i (Set.mem_univ i),hz⟩
  obtain ⟨x,hx,hval⟩ := hex
  refine ⟨x,hx,?_⟩
  have he : (∏ k, MvPolynomial.eval x (P k)) ≠ 0 := by simpa only [Q,map_prod] using hval
  exact fun k => (Finset.prod_ne_zero_iff.mp he) k (Finset.mem_univ k)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleOffsetParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

@[simp] theorem offsetParameter_zero (a : ℝ) : offsetParameter a 0=a := by
  simp only [offsetParameter,circleOffset_zero,circlePoint_parameter]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CirclePlacement
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic circular placement, prescribed arcs, restrictions, and existence of drawings. -/

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem circleLine_param (a b : ℝ) : circleLine a b (Zarankiewicz.circlePoint a) = 0 := by
  have ha := ne_of_gt (Zarankiewicz.circle_denominator_pos a)
  unfold circleLine Zarankiewicz.circlePoint
  field_simp
  ring

theorem circleLine_chord (a b t : ℝ) :
    circleLine a b (segmentPoint (Zarankiewicz.circlePoint a) (Zarankiewicz.circlePoint b) t) = 0 := by
  have ha := circleLine_param a b
  have hb := circleLine_param b a
  unfold circleLine at *
  change (1 - a * b) * ((1 - t) * (Zarankiewicz.circlePoint a).1 + t * (Zarankiewicz.circlePoint b).1) +
    (a + b) * ((1 - t) * (Zarankiewicz.circlePoint a).2 + t * (Zarankiewicz.circlePoint b).2) -
      (1 + a * b) = 0
  linear_combination (1 - t) * ha + t * hb

theorem circleConcurrency_of_lines (a b c d e f : ℝ) (z : Plane)
    (h₁ : circleLine a b z = 0) (h₂ : circleLine c d z = 0) (h₃ : circleLine e f z = 0) :
    circleConcurrency a b c d e f = 0 := by
  have he : 2 * circleConcurrency a b c d e f = 0 := by
    unfold circleConcurrency circleLine at *
    linear_combination
      -((1 - c * d) * (e + f) - (1 - e * f) * (c + d)) * h₁ -
      ((1 - e * f) * (a + b) - (1 - a * b) * (e + f)) * h₂ -
      ((1 - a * b) * (c + d) - (1 - c * d) * (a + b)) * h₃
  linarith

theorem circleConcurrencyPolynomial_eval {n : ℕ} (v : Fin 6 → Fin n) (t : Fin n → ℝ) :
    MvPolynomial.eval t (circleConcurrencyPolynomial v) =
      circleConcurrency (t (v 0)) (t (v 1)) (t (v 2)) (t (v 3)) (t (v 4)) (t (v 5)) := by
  simp [circleConcurrencyPolynomial, circleConcurrency]

theorem circleConcurrencyPolynomial_ne_zero {n : ℕ} (v : Fin 6 → Fin n)
    (hv : Function.Injective v) : circleConcurrencyPolynomial v ≠ 0 := by
  let t : Fin n → ℝ := fun i => if i = v 2 ∨ i = v 4 ∨ i = v 5 then 1 else 0
  have he : MvPolynomial.eval t (circleConcurrencyPolynomial v) = 1 := by
    rw [circleConcurrencyPolynomial_eval]
    simp only [t, hv.eq_iff]
    norm_num [circleConcurrency, Fin.ext_iff]
  intro hz
  rw [hz, map_zero] at he
  exact zero_ne_one he

theorem circle_configuration_exists (n : ℕ) : Nonempty (CircleConfiguration n) := by
  let I := {v : Fin 6 → Fin n // Function.Injective v}
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨t, ht, havoid⟩ := Zarankiewicz.exists_box_avoiding_polynomials
    (fun v : I => circleConcurrencyPolynomial v.val)
    (fun v => circleConcurrencyPolynomial_ne_zero v.val v.property)
    (fun i : Fin n => 2 * (i.val : ℝ) + 1) (fun i : Fin n => 2 * (i.val : ℝ) + 2)
    (by intro i; linarith)
  have htmono : StrictMono t := by
    intro i j hij
    have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    linarith [(ht i).2, (ht j).1]
  have htpos (i : Fin n) : 0 < t i := by
    have hnonneg : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    linarith [(ht i).1]
  let p := Zarankiewicz.circlePoint ∘ t
  have hp : Function.Injective p := Zarankiewicz.circlePoint_injective.comp htmono.injective
  have hcircle (i : Fin n) : squaredLength (p i) = 1 := Zarankiewicz.circlePoint_on_unit_circle (t i)
  refine ⟨{
    point := p
    injective := hp
    on_circle := hcircle
    cyclic_order := ?_
    no_antipodal := ?_
    no_triple_chords := ?_ }⟩
  · intro i j k hij hjk
    exact Zarankiewicz.circle_orient_pos (t i) (t j) (t k) (htmono hij) (htmono hjk)
  · intro i j _ he
    have hi : 0 < (p i).2 := div_pos (by linarith [htpos i]) (Zarankiewicz.circle_denominator_pos _)
    have hj : 0 < (p j).2 := div_pos (by linarith [htpos j]) (Zarankiewicz.circle_denominator_pos _)
    have hz := congrArg Prod.snd he
    change (p i).2 + (p j).2 = 0 at hz
    linarith
  · intro e f g hef heg hfg
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hEF := circle_chord_endpoints_distinct p hp hcircle e f hef z hz.1.1 hz.1.2
    have hEG := circle_chord_endpoints_distinct p hp hcircle e g heg z hz.1.1 hz.2
    have hFG := circle_chord_endpoints_distinct p hp hcircle f g hfg z hz.1.2 hz.2
    let v : Fin 6 → Fin n := ![e.val.1, e.val.2, f.val.1, f.val.2, g.val.1, g.val.2]
    have hv : Function.Injective v := by
      intro i j heq
      have he' := e.property
      have hf' := f.property
      have hg' := g.property
      fin_cases i <;> fin_cases j <;> norm_num [v, Fin.ext_iff] at heq ⊢ <;> omega
    have hne := havoid (⟨v, hv⟩ : I)
    rw [circleConcurrencyPolynomial_eval] at hne
    have hline (a : CompleteEdge n) (ha : z ∈ chordInterior p a) :
        circleLine (t a.val.1) (t a.val.2) z = 0 := by
      obtain ⟨u, _, rfl⟩ := ha
      exact circleLine_chord _ _ u
    apply hne
    exact circleConcurrency_of_lines _ _ _ _ _ _ z
      (hline e hz.1.1) (hline f hz.1.2) (hline g hz.2)

end Paper170

end
end

section

noncomputable section
namespace Paper170

variable {V E : Type}

theorem admissible_drawing_exists [Fintype V] [Fintype E] (G : Graph V E) : Nonempty (AdmissibleDrawing G) := by
  obtain ⟨C⟩ := circle_configuration_exists (Fintype.card V)
  exact ⟨restrictedCompleteAdmissible G (Fintype.equivFin V).toEmbedding (twoPageAdmissible C)⟩

theorem minimum_drawing_exists [Fintype V] [Fintype E] (G : Graph V E) :
    ∃ D : AdmissibleDrawing G, crossingCount D = ordinaryCrossingNumber G ∧
      ∀ A : AdmissibleDrawing G, crossingCount D ≤ crossingCount A := by
  obtain ⟨D₀⟩ := admissible_drawing_exists G
  obtain ⟨D, hD⟩ := Paper170Geometry.crossingCount_attainment D₀
  refine ⟨D, hD, fun A => ?_⟩
  rw [hD]
  exact Paper170Geometry.ordinaryCrossingNumber_le_count A

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Residues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residue fibers, same-page residues, and parity counts. -/

section

noncomputable section
namespace Paper170

theorem sameColorResidues_eq_intervals {n k : ℕ} (hn : 3 ≤ n)
    (hk : k ≤ n / 2) :
    sameColorResidues n k =
      Finset.Ico 0 (n / 2 - k) ∪ Finset.Ico (n / 2) (n - k) := by
  ext r
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range,
    residueColor, decide_eq_decide, Finset.mem_union, Finset.mem_Ico]
  by_cases hr : r < n
  · rw [Nat.mod_eq_of_lt hr]
    by_cases hrs : r + k < n
    · rw [Nat.mod_eq_of_lt hrs]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ r + k),
        Nat.mod_eq_of_lt (by omega : r + k - n < n)]
      omega
  · omega

theorem sameColorResidues_eq_intervals_large {n k : ℕ} (hn : 3 ≤ n)
    (hk : n / 2 < k) (hkn : k < n) :
    sameColorResidues n k =
      Finset.Ico (n - k) (n / 2) ∪ Finset.Ico (n + n / 2 - k) n := by
  ext r
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range,
    residueColor, decide_eq_decide, Finset.mem_union, Finset.mem_Ico]
  by_cases hr : r < n
  · rw [Nat.mod_eq_of_lt hr]
    by_cases hrs : r + k < n
    · rw [Nat.mod_eq_of_lt hrs]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ r + k),
        Nat.mod_eq_of_lt (by omega : r + k - n < n)]
      omega
  · omega

theorem sameColorResidues_card {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n - 2) :
    (sameColorResidues n k).card = n - 2 * min k (n - k) := by
  by_cases hh : k ≤ n / 2
  · rw [sameColorResidues_eq_intervals hn hh]
    have hd : Disjoint (Finset.Ico 0 (n / 2 - k)) (Finset.Ico (n / 2) (n - k)) := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_Ico]
      omega
    rw [Finset.card_union_of_disjoint hd, Nat.card_Ico, Nat.card_Ico,
      min_eq_left (by omega : k ≤ n - k)]
    omega
  · rw [sameColorResidues_eq_intervals_large hn (by omega) (by omega)]
    have hd : Disjoint (Finset.Ico (n - k) (n / 2)) (Finset.Ico (n + n / 2 - k) n) := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_Ico]
      omega
    rw [Finset.card_union_of_disjoint hd, Nat.card_Ico, Nat.card_Ico,
      min_eq_right (by omega : n - k ≤ k)]
    omega

theorem residueColor_add_half {m : ℕ} (hm : 0 < m) (r : ℕ) :
    residueColor (2 * m) (r + m) = !residueColor (2 * m) r := by
  have hr := Nat.mod_lt r (by omega : 0 < 2 * m)
  simp only [residueColor, Nat.mul_div_right m (by decide : 0 < 2)]
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : m < 2 * m)]
  by_cases hh : r % (2 * m) < m
  · rw [Nat.mod_eq_of_lt (by omega : r % (2 * m) + m < 2 * m)]
    simp [hh, show ¬r % (2 * m) + m < m by omega]
  · rw [Nat.mod_eq_sub_mod (by omega : 2 * m ≤ r % (2 * m) + m),
      Nat.mod_eq_of_lt (by omega : r % (2 * m) + m - 2 * m < 2 * m)]
    simp [hh, show r % (2 * m) + m - 2 * m < m by omega]

theorem sameColorResidues_half_shift {m k r : ℕ} (hm : 0 < m)
    (hr : r < 2 * m) :
    r ∈ sameColorResidues (2 * m) k ↔
      (r + m) % (2 * m) ∈ sameColorResidues (2 * m) k := by
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range, hr,
    Nat.mod_lt _ (by omega : 0 < 2 * m), true_and, residueColor_mod]
  rw [show residueColor (2 * m) ((r + m) % (2 * m) + k) =
      residueColor (2 * m) (r + k + m) by simp [residueColor, Nat.add_mod, Nat.add_right_comm]]
  rw [residueColor_add_half hm, residueColor_add_half hm]
  simp

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem residueFiber_card_odd {n b r : ℕ} (hn : Odd n) (hr : r < n) :
    (residueFiber n b r).card = 1 := by
  let f : Fin n → Fin n := fun a => ⟨(2 * a.val + b) % n, Nat.mod_lt _ (by omega)⟩
  have hi : Function.Injective f := by
    intro a c h
    have hmod : Nat.ModEq n (2 * a.val + b) (2 * c.val + b) := congrArg Fin.val h
    have he := (hmod.add_right_cancel' b).cancel_left_of_coprime hn.coprime_two_right
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt c.isLt] using he
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hi) ⟨r, hr⟩
  have hset : residueFiber n b r = {a.val} := by
    ext c
    simp only [residueFiber, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hcr⟩
      have he : f ⟨c, hc⟩ = f a := by
        rw [ha]
        exact Fin.ext hcr
      exact congrArg Fin.val (hi he)
    · rintro rfl
      exact ⟨a.isLt, congrArg Fin.val ha⟩
  rw [hset, Finset.card_singleton]

theorem add_mod_inj {n a c b : ℕ} (ha : a < n) (hc : c < n)
    (h : (a + b) % n = (c + b) % n) : a = c := by
  have he := Nat.ModEq.add_right_cancel' b h
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using he

theorem add_mod_surj {n r : ℕ} (hr : r < n) (b : ℕ) :
    ∃ a < n, (a + b) % n = r := by
  let f : Fin n → Fin n := fun a => ⟨(a.val + b) % n, Nat.mod_lt _ (by omega)⟩
  have hi : Function.Injective f := by
    intro a c h
    exact Fin.ext (add_mod_inj a.isLt c.isLt (congrArg Fin.val h))
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hi) ⟨r, hr⟩
  exact ⟨a.val, a.isLt, congrArg Fin.val ha⟩

theorem doubled_residue {m a b r : ℕ} :
    (2 * a + b) % (2 * m) = r ↔
      (a + b / 2) % m = r / 2 ∧ b % 2 = r % 2 := by
  have hh : (2 * a + b) % (2 * m) = b % 2 + 2 * ((a + b / 2) % m) := by
    rw [Nat.mod_mul]
    congr 1
    · omega
    · rw [show (2 * a + b) / 2 = a + b / 2 by omega]
  rw [hh]
  omega

theorem residueFiber_card_even {m b r : ℕ} (hm : 0 < m) (hr : r < 2 * m) :
    (residueFiber (2 * m) b r).card = if r % 2 = b % 2 then 2 else 0 := by
  by_cases hp : r % 2 = b % 2
  · rw [ite_eq_left hp]
    obtain ⟨a, ha, har⟩ := add_mod_surj (show r / 2 < m by omega) (b / 2)
    have hset : residueFiber (2 * m) b r = {a, a + m} := by
      ext c
      simp only [residueFiber, Finset.mem_filter, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton, doubled_residue]
      constructor
      · rintro ⟨hc, hcr, _⟩
        have he : c % m = a := add_mod_inj (Nat.mod_lt _ hm) ha
          (by simpa only [Nat.add_mod, Nat.mod_mod] using hcr.trans har.symm)
        by_cases hcm : c < m
        · left
          simpa only [Nat.mod_eq_of_lt hcm] using he
        · right
          rw [Nat.mod_eq_sub_mod (by omega : m ≤ c),
            Nat.mod_eq_of_lt (by omega : c - m < m)] at he
          omega
      · rintro (rfl | rfl)
        · exact ⟨by omega, har, hp.symm⟩
        · refine ⟨by omega, ?_, hp.symm⟩
          simpa only [Nat.add_right_comm a m (b / 2), Nat.add_mod_right] using har
    rw [hset, Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  · rw [ite_eq_right hp]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a
    simp only [residueFiber, Finset.mem_filter, Finset.mem_range, doubled_residue]
    rintro ⟨_, _, he⟩
    exact hp he.symm

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem parity_balance_of_involution (s : Finset ℕ) (f : ℕ → ℕ) (c : ℕ)
    (hmap : ∀ r ∈ s, f r ∈ s) (hinv : ∀ r ∈ s, f (f r) = r)
    (hpar : ∀ r ∈ s, (f r + c) % 2 ≠ (r + c) % 2) :
    (s.filter (fun r => (r + c) % 2 = 0)).card =
      (s.filter (fun r => (r + c) % 2 = 1)).card := by
  apply Finset.card_nbij' f f
  · intro r hr
    obtain ⟨hs, he⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hmap r hs, by have := hpar r hs; omega⟩
  · intro r hr
    obtain ⟨hs, he⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hmap r hs, by have := hpar r hs; omega⟩
  · intro r hr
    exact hinv r (Finset.mem_filter.mp hr).1
  · intro r hr
    exact hinv r (Finset.mem_filter.mp hr).1

theorem interval_parity_balance {a b : ℕ} (heven : Even (b - a)) (c : ℕ) :
    ((Finset.Ico a b).filter (fun r => (r + c) % 2 = 0)).card =
      ((Finset.Ico a b).filter (fun r => (r + c) % 2 = 1)).card := by
  obtain ⟨t, ht⟩ := heven
  let f : ℕ → ℕ := fun r => if (r - a) % 2 = 0 then r + 1 else r - 1
  apply parity_balance_of_involution (Finset.Ico a b) f c
  · intro r hr
    simp only [Finset.mem_Ico] at hr ⊢
    dsimp [f]
    split_ifs <;> omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    dsimp [f]
    split_ifs <;> omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    dsimp [f]
    split_ifs <;> omega

theorem firstGapParity_balance {k : ℕ} (hk : Odd k) (b : ℕ) :
    (firstGapParity k b 0).card = (firstGapParity k b 1).card := by
  have heven : Even (k - 1) := by
    rw [Nat.even_iff]
    obtain ⟨t, ht⟩ := hk
    omega
  have heq : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    obtain ⟨t, ht⟩ := hk
    omega
  simpa only [firstGapParity, heq] using interval_parity_balance heven b

theorem parity_balance_union (s t : Finset ℕ) (hd : Disjoint s t)
    (hs : (s.filter (fun r => r % 2 = 0)).card = (s.filter (fun r => r % 2 = 1)).card)
    (ht : (t.filter (fun r => r % 2 = 0)).card = (t.filter (fun r => r % 2 = 1)).card) :
    ((s ∪ t).filter (fun r => r % 2 = 0)).card =
      ((s ∪ t).filter (fun r => r % 2 = 1)).card := by
  have hdis (p : ℕ) : Disjoint (s.filter (fun r => r % 2 = p))
      (t.filter (fun r => r % 2 = p)) := hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  simp only [Finset.filter_union, Finset.card_union_of_disjoint (hdis 0),
    Finset.card_union_of_disjoint (hdis 1), hs, ht]

theorem sameColorResidues_parity_balance {m k : ℕ} (hm : 0 < m)
    (hk : 2 ≤ k) (hkn : k ≤ 2 * m - 2) (hparity : Odd m ∨ Even k) :
    (sameColorResiduesParity (2 * m) k 0).card =
      (sameColorResiduesParity (2 * m) k 1).card := by
  by_cases hmo : Odd m
  · obtain ⟨t, ht⟩ := hmo
    let f : ℕ → ℕ := fun r => if r < m then r + m else r - m
    have hform (r : ℕ) (hr : r < 2 * m) : f r = (r + m) % (2 * m) := by
      dsimp [f]
      split_ifs with h
      · rw [Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    apply parity_balance_of_involution (sameColorResidues (2 * m) k) f 0
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      rw [hform r hrl]
      exact (sameColorResidues_half_shift hm hrl).mp hr
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      dsimp [f]
      split_ifs <;> omega
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      dsimp [f]
      split_ifs <;> omega
  · have hme : Even m := Nat.not_odd_iff_even.mp hmo
    have hke : Even k := hparity.resolve_left hmo
    have hm₂ : 3 ≤ 2 * m := by omega
    have even_diff (a b : ℕ) (ha : Even a) (hb : Even b) : Even (a - b) := by
      rw [Nat.even_iff] at *
      omega
    unfold sameColorResiduesParity
    by_cases hhalf : k ≤ m
    · rw [sameColorResidues_eq_intervals hm₂ (by simpa using hhalf)]
      simp only [Nat.mul_div_right m (by decide : 0 < 2)]
      apply parity_balance_union
      · apply Finset.disjoint_left.mpr
        simp only [Finset.mem_Ico]
        omega
      · simpa using interval_parity_balance (a := 0) (b := m - k)
          (by simpa using even_diff m k hme hke) 0
      · have he : Even (2 * m - k - m) := by
          apply even_diff _ _ (even_diff _ _ (by simp) hke) hme
        simpa using interval_parity_balance he 0
    · rw [sameColorResidues_eq_intervals_large hm₂ (by simpa using Nat.lt_of_not_ge hhalf) (by omega)]
      simp only [Nat.mul_div_right m (by decide : 0 < 2)]
      apply parity_balance_union
      · apply Finset.disjoint_left.mpr
        simp only [Finset.mem_Ico]
        omega
      · have he : Even (m - (2 * m - k)) := even_diff _ _ hme (even_diff _ _ (by simp) hke)
        simpa using interval_parity_balance he 0
      · have he : Even (2 * m - (2 * m + m - k)) :=
          even_diff _ _ (by simp) (even_diff _ _
            (by simpa only [two_mul, add_assoc] using hme.add hme |>.add hme) hke)
        simpa using interval_parity_balance he 0

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclic gap enumeration and the exact Harary–Hill crossing-tuple count. -/

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem mem_naturalCrossingTuples {n : ℕ} {v : Fin 4 → ℕ} :
    v ∈ naturalCrossingTuples n ↔
      v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧ v 3 < n ∧
        residueColor n (v 0 + v 2) = residueColor n (v 1 + v 3) := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨_, hw, hc⟩ := Finset.mem_filter.mp hw
    exact ⟨hw (by decide : (0 : Fin 4) < 1), hw (by decide : (1 : Fin 4) < 2),
      hw (by decide : (2 : Fin 4) < 3), (w 3).isLt, hc⟩
  · rintro ⟨h₀, h₁, h₂, h₃, hc⟩
    have hb (i : Fin 4) : v i < n := by fin_cases i <;> dsimp <;> omega
    let w : Fin 4 → Fin n := fun i => ⟨v i, hb i⟩
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hc⟩, rfl⟩
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp only [w, Fin.mk_lt_mk] <;> assumption

theorem naturalCrossingTuples_card (n : ℕ) :
    (naturalCrossingTuples n).card = (crossingTuples n).card := by
  apply Finset.card_image_of_injective
  intro v w h
  funext i
  exact Fin.ext (congrFun h i)

theorem mem_cyclicRecords {n k a g h : ℕ} :
    (⟨k, a, g, h⟩ : CyclicRecord) ∈ cyclicRecords n ↔
      2 ≤ k ∧ k ≤ n - 2 ∧ a < n ∧ 1 ≤ g ∧ g ≤ k - 1 ∧
        1 ≤ h ∧ h ≤ n - k - 1 ∧
          residueColor n (2 * a + g + h) = residueColor n (2 * a + g + h + k) := by
  simp [cyclicRecords, sameColorGapTuples, and_assoc]

theorem residueColor_shift_eq {n x y : ℕ} (t : ℕ) (h : x + t * n = y) :
    residueColor n x = residueColor n y := by
  rw [← h]
  simp [residueColor, Nat.add_mod]

theorem cyclicToOrdered_spec {n k a g h : ℕ} (hk : 2 ≤ k) (_hkn : k ≤ n - 2)
    (ha : a < n) (hg : 1 ≤ g) (hgk : g ≤ k - 1)
    (hh : 1 ≤ h) (hhn : h ≤ n - k - 1) :
    let v := (cyclicToOrdered n ⟨k, a, g, h⟩).2
    v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧ v 3 < n ∧
      (residueColor n (v 0 + v 2) = residueColor n (v 1 + v 3) ↔
        residueColor n (2 * a + g + h) = residueColor n (2 * a + g + h + k)) := by
  by_cases hd : a + k + h < n
  · simp only [cyclicToOrdered, hd, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
    rw [show a + (a + g + h) = 2 * a + g + h by omega,
      show a + g + (a + k + h) = 2 * a + g + h + k by omega]
  · by_cases hc : a + g + h < n
    · simp only [cyclicToOrdered, hd, hc, ↓reduceIte, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
      rw [residueColor_shift_eq 1 (show (a + k + h - n + (a + g)) + 1 * n =
        2 * a + g + h + k by omega)]
      have he : a + (a + g + h) = 2 * a + g + h := by omega
      rw [he, eq_comm]
    · by_cases hb : a + g < n
      · simp only [cyclicToOrdered, hd, hc, hb, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
        rw [residueColor_shift_eq 1 (show (a + g + h - n + a) + 1 * n =
          2 * a + g + h by omega),
          residueColor_shift_eq 1 (show (a + k + h - n + (a + g)) + 1 * n =
          2 * a + g + h + k by omega)]
      · simp only [cyclicToOrdered, hd, hc, hb, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        refine ⟨by omega, by omega, by omega, ha, ?_⟩
        rw [residueColor_shift_eq 2 (show (a + g - n + (a + k + h - n)) + 2 * n =
          2 * a + g + h + k by omega),
          residueColor_shift_eq 1 (show (a + g + h - n + a) + 1 * n =
          2 * a + g + h by omega), eq_comm]

theorem orderedToCyclic_bounds {n : ℕ} (j : Fin 4) (v : Fin 4 → ℕ)
    (h₀ : v 0 < v 1) (h₁ : v 1 < v 2) (h₂ : v 2 < v 3) (h₃ : v 3 < n) :
    let p := orderedToCyclic n (j, v)
    2 ≤ p.1 ∧ p.1 ≤ n - 2 ∧ p.2.1 < n ∧ 1 ≤ p.2.2.1 ∧
      p.2.2.1 ≤ p.1 - 1 ∧ 1 ≤ p.2.2.2 ∧ p.2.2.2 ≤ n - p.1 - 1 := by
  fin_cases j <;> simp [orderedToCyclic] <;> omega

theorem orderedToCyclic_inverse {n : ℕ} (j : Fin 4) (v : Fin 4 → ℕ)
    (h₀ : v 0 < v 1) (h₁ : v 1 < v 2) (h₂ : v 2 < v 3) (h₃ : v 3 < n) :
    cyclicToOrdered n (orderedToCyclic n (j, v)) = (j, v) := by
  fin_cases j <;> simp (disch := omega) [orderedToCyclic, cyclicToOrdered]
  all_goals split_ifs <;> try omega
  all_goals
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp <;> omega

theorem cyclicToOrdered_inverse {n k a g h : ℕ} (hk : 2 ≤ k) (_hkn : k ≤ n - 2)
    (ha : a < n) (hg : 1 ≤ g) (hgk : g ≤ k - 1)
    (hh : 1 ≤ h) (hhn : h ≤ n - k - 1) :
    orderedToCyclic n (cyclicToOrdered n ⟨k, a, g, h⟩) = ⟨k, a, g, h⟩ := by
  unfold cyclicToOrdered
  dsimp only
  split_ifs <;> simp [orderedToCyclic] <;> omega

theorem cyclicToOrdered_mem {n : ℕ} {p : CyclicRecord} (hp : p ∈ cyclicRecords n) :
    cyclicToOrdered n p ∈ (Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n := by
  rcases p with ⟨k, a, g, h⟩
  obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn, hc⟩ := mem_cyclicRecords.mp hp
  obtain ⟨h₀, h₁, h₂, h₃, he⟩ := cyclicToOrdered_spec hk hkn ha hg hgk hh hhn
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
    mem_naturalCrossingTuples.mpr ⟨h₀, h₁, h₂, h₃, he.mpr hc⟩⟩

theorem orderedToCyclic_mem {n : ℕ} {q : Fin 4 × (Fin 4 → ℕ)}
    (hq : q ∈ (Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n) :
    orderedToCyclic n q ∈ cyclicRecords n := by
  rcases q with ⟨j, v⟩
  obtain ⟨h₀, h₁, h₂, h₃, hc⟩ := mem_naturalCrossingTuples.mp (Finset.mem_product.mp hq).2
  obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn⟩ := orderedToCyclic_bounds j v h₀ h₁ h₂ h₃
  apply mem_cyclicRecords.mpr
  refine ⟨hk, hkn, ha, hg, hgk, hh, hhn, ?_⟩
  have he := (cyclicToOrdered_spec hk hkn ha hg hgk hh hhn).2.2.2.2
  rw [show (⟨(orderedToCyclic n (j, v)).1, (orderedToCyclic n (j, v)).2.1,
      (orderedToCyclic n (j, v)).2.2.1, (orderedToCyclic n (j, v)).2.2.2⟩ : CyclicRecord) =
      orderedToCyclic n (j, v) from rfl, orderedToCyclic_inverse j v h₀ h₁ h₂ h₃] at he
  exact he.mp hc

theorem crossingTuples_cyclic_count {n : ℕ} (_hn : 3 ≤ n) :
    4 * (crossingTuples n).card =
      ∑ k ∈ Finset.Icc 2 (n - 2), (sameColorGapTuples n k).card := by
  have hcard : (cyclicRecords n).card =
      ((Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n).card := by
    apply Finset.card_nbij' (cyclicToOrdered n) (orderedToCyclic n)
    · exact fun _ hp => cyclicToOrdered_mem hp
    · exact fun _ hq => orderedToCyclic_mem hq
    · rintro ⟨k, a, g, h⟩ hp
      obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn, _⟩ := mem_cyclicRecords.mp hp
      exact cyclicToOrdered_inverse hk hkn ha hg hgk hh hhn
    · rintro ⟨j, v⟩ hq
      obtain ⟨h₀, h₁, h₂, h₃, _⟩ := mem_naturalCrossingTuples.mp (Finset.mem_product.mp hq).2
      exact orderedToCyclic_inverse j v h₀ h₁ h₂ h₃
  simpa only [cyclicRecords, Finset.card_sigma, Finset.card_product,
    Finset.card_univ, Fintype.card_fin, naturalCrossingTuples_card] using hcard.symm

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem startingLabels_card_eq_sum {n : ℕ} (hn : 0 < n) (k b : ℕ) :
    (startingLabels n k b).card =
      ∑ r ∈ sameColorResidues n k, (residueFiber n b r).card := by
  unfold residueFiber
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext a
  simp [startingLabels, sameColorResidues, residueColor,
    Nat.mod_lt _ hn, Nat.add_mod]

theorem startingLabels_card_odd {n : ℕ} (hn : Odd n) (k b : ℕ) :
    (startingLabels n k b).card = (sameColorResidues n k).card := by
  have hpos : 0 < n := by obtain ⟨t, ht⟩ := hn; omega
  rw [startingLabels_card_eq_sum hpos]
  calc
    (∑ r ∈ sameColorResidues n k, (residueFiber n b r).card) =
        ∑ _r ∈ sameColorResidues n k, 1 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact residueFiber_card_odd hn (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    _ = _ := by simp

theorem startingLabels_card_even {m : ℕ} (hm : 0 < m) (k b : ℕ) :
    (startingLabels (2 * m) k b).card = 2 * (sameColorResiduesParity (2 * m) k (b % 2)).card := by
  rw [startingLabels_card_eq_sum (by omega)]
  calc
    (∑ r ∈ sameColorResidues (2 * m) k, (residueFiber (2 * m) b r).card) =
        ∑ r ∈ sameColorResidues (2 * m) k, if r % 2 = b % 2 then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact residueFiber_card_even hm (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    _ = _ := by rw [← Finset.sum_filter]; simp [sameColorResiduesParity, mul_comm]

theorem parity_partition (s : Finset ℕ) (b : ℕ) :
    (s.filter (fun r => (r + b) % 2 = 0)).card +
      (s.filter (fun r => (r + b) % 2 = 1)).card = s.card := by
  have he : s.filter (fun r => ¬(r + b) % 2 = 0) = s.filter (fun r => (r + b) % 2 = 1) := by
    ext r
    rcases Nat.mod_two_eq_zero_or_one (r + b) with h | h <;> simp [h]
  rw [← he]
  exact Finset.card_filter_add_card_filter_not (s := s) _

theorem startingLabels_card_even_balanced {m k : ℕ} (hm : 0 < m)
    (hk : 2 ≤ k) (hkn : k ≤ 2 * m - 2) (hparity : Odd m ∨ Even k) (b : ℕ) :
    (startingLabels (2 * m) k b).card = (sameColorResidues (2 * m) k).card := by
  rw [startingLabels_card_even hm]
  have hbal := sameColorResidues_parity_balance hm hk hkn hparity
  have htotal := parity_partition (sameColorResidues (2 * m) k) 0
  simp only [Nat.add_zero] at htotal
  change (sameColorResiduesParity (2 * m) k 0).card +
    (sameColorResiduesParity (2 * m) k 1).card = _ at htotal
  have hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  rcases hb with hb | hb <;> rw [hb] <;> omega

theorem sum_parity_weights (s : Finset ℕ) (b x y : ℕ)
    (hbal : (s.filter (fun r => (r + b) % 2 = 0)).card =
      (s.filter (fun r => (r + b) % 2 = 1)).card) :
    (∑ r ∈ s, 2 * (if (r + b) % 2 = 0 then x else y)) = s.card * (x + y) := by
  have he : s.filter (fun r => ¬(r + b) % 2 = 0) = s.filter (fun r => (r + b) % 2 = 1) := by
    ext r
    rcases Nat.mod_two_eq_zero_or_one (r + b) with h | h <;> simp [h]
  rw [← Finset.mul_sum, Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, he]
  rw [← parity_partition s b, hbal]
  ring

theorem startingLabels_sum_odd_gap {m k : ℕ} (hm : 0 < m) (hk : Odd k) (b : ℕ) :
    (∑ g ∈ Finset.Icc 1 (k - 1), (startingLabels (2 * m) k (g + b)).card) =
      (k - 1) * (sameColorResidues (2 * m) k).card := by
  simp_rw [startingLabels_card_even hm]
  have hfun (g : ℕ) : (sameColorResiduesParity (2 * m) k ((g + b) % 2)).card =
      if (g + b) % 2 = 0 then (sameColorResiduesParity (2 * m) k 0).card
      else (sameColorResiduesParity (2 * m) k 1).card := by
    rcases Nat.mod_two_eq_zero_or_one (g + b) with h | h <;> simp [h]
  simp_rw [hfun]
  rw [sum_parity_weights _ _ _ _ (firstGapParity_balance hk b)]
  have htotal := parity_partition (sameColorResidues (2 * m) k) 0
  simp only [Nat.add_zero] at htotal
  change (sameColorResiduesParity (2 * m) k 0).card +
    (sameColorResiduesParity (2 * m) k 1).card = _ at htotal
  rw [htotal, Nat.card_Icc]
  congr 1

theorem sameColorGapTuples_card_eq_sum (n k : ℕ) :
    (sameColorGapTuples n k).card =
      ∑ g₂ ∈ Finset.Icc 1 (n - k - 1), ∑ g₁ ∈ Finset.Icc 1 (k - 1),
        (startingLabels n k (g₁ + g₂)).card := by
  simp only [sameColorGapTuples, startingLabels, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product, Nat.add_assoc]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext g₁; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem sameColorGapTuples_card {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n - 2) :
    (sameColorGapTuples n k).card = (k - 1) * (n - k - 1) *
      (sameColorResidues n k).card := by
  rw [sameColorGapTuples_card_eq_sum]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    have heq : n = 2 * m := by omega
    clear hm
    subst n
    have hmp : 0 < m := by omega
    by_cases hpar : Odd m ∨ Even k
    · simp_rw [startingLabels_card_even_balanced hmp hk hkn hpar]
      simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
      have h₁ : k - 1 + 1 - 1 = k - 1 := by omega
      have h₂ : 2 * m - k - 1 + 1 - 1 = 2 * m - k - 1 := by omega
      rw [h₁, h₂]
      ring
    · have hko : Odd k := Nat.not_even_iff_odd.mp (fun h => hpar (Or.inr h))
      simp_rw [startingLabels_sum_odd_gap hmp hko]
      simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
      have h₂ : 2 * m - k - 1 + 1 - 1 = 2 * m - k - 1 := by omega
      rw [h₂]
      ring
  · simp_rw [startingLabels_card_odd ho]
    simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
    have h₁ : k - 1 + 1 - 1 = k - 1 := by omega
    have h₂ : n - k - 1 + 1 - 1 = n - k - 1 := by omega
    rw [h₁, h₂]
    ring

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem crossingTuples_card {n : ℕ} (hn : 3 ≤ n) :
    (crossingTuples n).card = hill n := by
  have hcount : 4 * (crossingTuples n).card =
      (n / 2) * (n / 2 - 1) * (n - n / 2 - 1) * (n - n / 2 - 2) := by
    rw [crossingTuples_cyclic_count hn]
    calc
      (∑ k ∈ Finset.Icc 2 (n - 2), (sameColorGapTuples n k).card) =
          ∑ k ∈ Finset.Icc 2 (n - 2),
            (k - 1) * (n - k - 1) * (n - 2 * min k (n - k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk₁ := (Finset.mem_Icc.mp hk).1
        have hk₂ := (Finset.mem_Icc.mp hk).2
        rw [sameColorGapTuples_card hn hk₁ hk₂, sameColorResidues_card hn hk₁ hk₂]
      _ = _ := by rw [cyclic_count_pairing hn, crossing_sum_telescope hn]
  have h₁ : n - n / 2 - 1 = (n - 1) / 2 := by omega
  have h₂ : n / 2 - 1 = (n - 2) / 2 := by omega
  have h₃ : n - n / 2 - 2 = (n - 3) / 2 := by omega
  rw [h₁, h₂, h₃] at hcount
  have hp : n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) =
      4 * (crossingTuples n).card := by rw [hcount]; ring
  rw [hill, hp]
  omega

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_TwoPage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting actual crossing points of the explicit two-page drawing. -/

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

lemma twoPage_meeting_chords {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e f : CompleteEdge n) (x : Plane)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val) ∧
      ∃ y, y ∈ chordInterior C.point e ∩ chordInterior C.point f ∧
        x = if residueColor n (e.val.1.val + e.val.2.val) then y else inversion y := by
  rw [twoPage_edgeInterior C D hD e] at he
  rw [twoPage_edgeInterior C D hD f] at hf
  cases hec : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hfc : residueColor n (f.val.1.val + f.val.2.val)
  · simp only [hec, Bool.false_eq_true, ↓reduceIte] at he
    simp only [hfc, Bool.false_eq_true, ↓reduceIte] at hf
    obtain ⟨y, hy, rfl⟩ := he
    obtain ⟨z, hz, hzy⟩ := hf
    have hzy' : z = y := inversion_involutive.injective hzy
    subst z
    exact ⟨rfl, y, ⟨hy, hz⟩, rfl⟩
  · simp only [hec, Bool.false_eq_true, ↓reduceIte] at he
    simp only [hfc, ↓reduceIte] at hf
    have h1 := C.inverted_chord_outside e he
    have h2 := C.chord_inside f hf
    linarith
  · simp only [hec, ↓reduceIte] at he
    simp only [hfc, Bool.false_eq_true, ↓reduceIte] at hf
    have h1 := C.chord_inside e he
    have h2 := C.inverted_chord_outside f hf
    linarith
  · simp only [hec, ↓reduceIte] at he
    simp only [hfc, ↓reduceIte] at hf
    exact ⟨rfl, x, ⟨he, hf⟩, rfl⟩

lemma chord_meeting_alternates {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) (y : Plane)
    (hy : y ∈ chordInterior C.point e ∩ chordInterior C.point f) :
    ((e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)) ∧
      y = lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) := by
  rw [circle_chord_intersection C e f hef] at hy
  split_ifs at hy with h
  · exact ⟨h, hy⟩
  · exact hy.elim

lemma twoPage_meeting_alternates {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val) ∧
    ((e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)) ∧
    x = if residueColor n (e.val.1.val + e.val.2.val) then
      lineIntersectionPoint (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2)
      else inversion (lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2)) := by
  obtain ⟨hc, y, hy, hx⟩ := twoPage_meeting_chords C D hD e f x he hf
  obtain ⟨ho, rfl⟩ := chord_meeting_alternates C e f hef y hy
  exact ⟨hc, ho, hx⟩

lemma pagePoint_mem_edge {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e : CompleteEdge n) (y : Plane) (hy : y ∈ chordInterior C.point e) :
    (if residueColor n (e.val.1.val + e.val.2.val) then y else inversion y) ∈
      edgeInterior D.toContinuousDrawing e := by
  rw [twoPage_edgeInterior C D hD]
  cases h : residueColor n (e.val.1.val + e.val.2.val)
  · exact ⟨y, hy, rfl⟩
  · exact hy

lemma ordered_chord_meeting {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n)
    (ho : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) :
    lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
      (C.point f.val.1) (C.point f.val.2) ∈ chordInterior C.point e ∩ chordInterior C.point f := by
  have hef : e ≠ f := by intro h; subst f; exact (lt_irrefl _ ho.1)
  rw [circle_chord_intersection C e f hef, ite_eq_left (Or.inl ho)]
  exact Set.mem_singleton _

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

lemma tuple_edges_ne {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) :
    tupleFirstEdge v hv ≠ tupleSecondEdge v hv := by
  intro h
  exact (ne_of_lt (hv (by decide : (0 : Fin 4) < 1)))
    (congrArg (fun e => e.val.1) h)

lemma tuple_point_membership {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (v : Fin 4 → Fin n) (hv : v ∈ crossingTuples n) :
    let hm := (Finset.mem_filter.mp hv).2.1
    crossingTuplePoint C v ∈ edgeInterior D.toContinuousDrawing (tupleFirstEdge v hm) ∧
      crossingTuplePoint C v ∈ edgeInterior D.toContinuousDrawing (tupleSecondEdge v hm) := by
  let hm := (Finset.mem_filter.mp hv).2.1
  have hc := (Finset.mem_filter.mp hv).2.2
  have hy := ordered_chord_meeting C (tupleFirstEdge v hm) (tupleSecondEdge v hm)
    ⟨hm (by decide : (0 : Fin 4) < 1), hm (by decide : (1 : Fin 4) < 2),
      hm (by decide : (2 : Fin 4) < 3)⟩
  constructor
  · exact pagePoint_mem_edge C D hD (tupleFirstEdge v hm) _ hy.1
  · have h := pagePoint_mem_edge C D hD (tupleSecondEdge v hm) _ hy.2
    change (if residueColor n ((v 1).val + (v 3).val) then _ else _) ∈ _ at h
    rw [← hc] at h
    exact h

lemma ordered_pair_tuple {n : ℕ} (C : CircleConfiguration n) (e f : CompleteEdge n)
    (ho : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2)
    (hc : residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val)) :
    ∃ v ∈ crossingTuples n, crossingTuplePoint C v =
      if residueColor n (e.val.1.val + e.val.2.val) then
        lineIntersectionPoint (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2)
      else inversion (lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2)) := by
  let v : Fin 4 → Fin n := ![e.val.1, f.val.1, e.val.2, f.val.2]
  refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact ho.1
    · exact ho.2.1
    · exact ho.2.2
  · exact hc

lemma crossingTuplePoint_surjOn {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    SurjOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n))
      (crossingPoints D.toContinuousDrawing) := by
  rintro x ⟨e, f, hef, he, hf⟩
  obtain ⟨hc, ho, hx⟩ := twoPage_meeting_alternates C D hD e f hef x he hf
  rcases ho with ho | ho
  · obtain ⟨v, hv, hp⟩ := ordered_pair_tuple C e f ho hc
    exact ⟨v, hv, hp.trans hx.symm⟩
  · obtain ⟨_, _, hx'⟩ := twoPage_meeting_alternates C D hD f e hef.symm x hf he
    obtain ⟨v, hv, hp⟩ := ordered_pair_tuple C f e ho hc.symm
    exact ⟨v, hv, hp.trans hx'.symm⟩

lemma crossingTuplePoint_injOn {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    InjOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n)) := by
  intro v hv w hw hpoint
  let hv' := (Finset.mem_filter.mp hv).2.1
  let hw' := (Finset.mem_filter.mp hw).2.1
  have hpv := tuple_point_membership C D hD v hv
  have hpw := tuple_point_membership C D hD w hw
  rw [← hpoint] at hpw
  have hinc := Paper170Geometry.crossing_incident_iff D (crossingTuplePoint C v)
    (tupleFirstEdge v hv') (tupleSecondEdge v hv') (tuple_edges_ne v hv') hpv.1 hpv.2
  have he := (hinc (tupleFirstEdge w hw')).mp hpw.1
  have hf := (hinc (tupleSecondEdge w hw')).mp hpw.2
  rcases he with he | he <;> rcases hf with hf | hf
  · exact (tuple_edges_ne w hw' (he.trans hf.symm)).elim
  · have h0 := congrArg (fun e => e.val.1) he
    have h2 := congrArg (fun e => e.val.2) he
    have h1 := congrArg (fun e => e.val.1) hf
    have h3 := congrArg (fun e => e.val.2) hf
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · have h0 : w 0 = v 1 := congrArg (fun e => e.val.1) he
    have h1 : w 1 = v 0 := congrArg (fun e => e.val.1) hf
    have hlt := hw' (by decide : (0 : Fin 4) < 1)
    rw [h0, h1] at hlt
    exact (lt_asymm (hv' (by decide : (0 : Fin 4) < 1)) hlt).elim
  · exact (tuple_edges_ne w hw' (he.trans hf.symm)).elim

theorem two_page_crossing_bijection {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    BijOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n))
      (crossingPoints D.toContinuousDrawing) := by
  refine ⟨?_, crossingTuplePoint_injOn C D hD, crossingTuplePoint_surjOn C D hD⟩
  intro v hv
  have hp := tuple_point_membership C D hD v hv
  exact ⟨_, _, tuple_edges_ne _ _, hp.1, hp.2⟩

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem two_page_crossing_count {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    crossingCount D = (crossingTuples n).card := by
  have h := (two_page_crossing_bijection C D hD).ncard_eq
  simpa [crossingCount, Set.ncard_eq_toFinset_card _ D.crossings_finite] using h.symm

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem complete_graph_upper_drawing (n : ℕ) :
    ∃ D : AdmissibleDrawing (completeGraph n), crossingCount D = (crossingTuples n).card := by
  obtain ⟨C⟩ := circle_configuration_exists n
  obtain ⟨D, hD⟩ := two_page_drawing_exists C
  exact ⟨D, two_page_crossing_count C D hD⟩

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd and even lower bounds, explicit attainment, and the ordinary complete-graph crossing formula. -/

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

theorem complete_graph_upper_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ D : AdmissibleDrawing (completeGraph n), crossingCount D = hill n := by
  obtain ⟨D, hD⟩ := complete_graph_upper_drawing n
  exact ⟨D, hD.trans (crossingTuples_card hn)⟩

theorem complete_graph_crossing_number_oai (n : ℕ) (hn : 3 ≤ n) :
    ordinaryCrossingNumber (completeGraph n) = hill n := by
  obtain ⟨D, hD⟩ := complete_graph_upper_bound n hn
  apply Nat.le_antisymm
  · rw [← hD]
    exact Paper170Geometry.ordinaryCrossingNumber_le_count D
  · obtain ⟨A,hA,_⟩ := minimum_drawing_exists (completeGraph n)
    rw [← hA]
    exact complete_graph_lower_bound n hn A

end Paper170

end
end

end OAI
end

theorem solution : type_of% @OAI.Paper170.complete_graph_crossing_number_oai := @OAI.Paper170.complete_graph_crossing_number_oai
