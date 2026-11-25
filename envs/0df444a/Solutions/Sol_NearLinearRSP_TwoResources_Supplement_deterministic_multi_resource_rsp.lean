-- Prove2me | solution 1 for NearLinearRSP.TwoResources.Supplement.deterministic_multi_resource_rsp
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-25T09:31:34.614803+00:00
-- url     : https://prove2.me/submissions/cb7b1c4f-67db-4ec1-a8cb-73171267870f

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_TableMachine
import Theorems.Thm_NearLinearRSP_TwoResources_Implementation_initialization_and_expectation_correct
import Theorems.Thm_NearLinearRSP_TwoResources_Supplement_bounded_ram_preprocessing

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

universe u_1

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Structured

theorem compiled_preprocessing :
  ∀ {input : RAMInput} {c : Cmd} {t : Store} {n : ℕ}
    (h : Run input c initialStore t n),
  ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input initialState out steps ∧ steps ≤ n + 1 ∧
      Store.ofRAM out = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.1.1.2.2

theorem compiled_query :
  ∀ {input : RAMInput} {c : Cmd} {t : Store} {n : ℕ}
    (snapshot : RAMState) (target : ℕ)
    (h : Run input c (queryStore snapshot target) t n),
  ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input (queryStart snapshot target) out steps ∧
      steps ≤ n + 1 ∧ Store.ofRAM out = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.1.2.1

end Structured
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

theorem run_atoms :
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (Cmd.atoms as) s (evalAtoms input as s) as.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.1.2.1

@[ext] theorem Store.ext :
  ∀ {s t : Store} (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm),
  s = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory
namespace RSP.Tails

theorem mass_nonneg :
  ∀ (r : ℝ≥0) (n : ℕ),
  0 ≤ mass r n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.2.2.1

theorem mass_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (mass r) 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.1.1

theorem poisson_pgf_hasSum :
  ∀ (r : ℝ≥0) (z : ℝ),
  HasSum (fun n : ℕ => mass r n * z ^ n) (Real.exp ((r : ℝ) * (z - 1))) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.1.2.1

theorem firstMoment_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * (n : ℝ)) (r : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.2.1

theorem secondMoment_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * (n : ℝ) ^ 2) ((r : ℝ) ^ 2 + (r : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.2.2.2

theorem completeness_ratio_le :
  ∀ (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2),
  (q / (1 + ε / 2)) / (q - q / (1 + ε / 2)) ^ 2 ≤
      1 / (8 * (k : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.1.1.2.2

end RSP.Tails
end

set_option autoImplicit false
section
set_option autoImplicit false
open NearLinearRSP.TwoResources
namespace RSP.PoissonBridge

theorem poissonCountMass_nonneg :
  ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℕ),
  0 ≤ ActuarialValuation.poissonCountMass r n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.1.2.2

theorem poissonCountMass_hasSum :
  ∀ (r : ℝ) (hr : 0 ≤ r),
  HasSum (ActuarialValuation.poissonCountMass r) 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.2.1

end RSP.PoissonBridge
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem activeVertices_edge_right :
  ∀ (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges),
  v ∈ activeVertices I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem pathWeight_cons_cons :
  ∀ (w : ℕ → ℕ → ℝ≥0) (a b : ℕ) (P : List ℕ),
  pathWeight w (a :: b :: P) = (w a b : ℝ) + pathWeight w (b :: P) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.2.1

theorem pathWeight_nonneg :
  ∀ (w : ℕ → ℕ → ℝ≥0) (P : List ℕ),
  0 ≤ pathWeight w P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.2.2

theorem IsPath.exists_simple :
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n),
  ∃ Q : List ℕ, IsPath G s t Q ∧ Q.Nodup ∧ Q.length ≤ G.n ∧
      Q ⊆ P ∧ ∀ w : ℕ → ℕ → ℝ≥0, pathWeight w Q ≤ pathWeight w P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.1.1

theorem IsPath.weight_le_n_mul :
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) (hnd : P.Nodup)
    (w : ℕ → ℕ → ℝ≥0) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ u v, (u, v) ∈ G.edges → (w u v : ℝ) ≤ M),
  pathWeight w P ≤ (G.n : ℝ) * M :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem treeRun_succ :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue),
  treeRun I allow w (n + 1) S = treePop I allow w (treeRun I allow w n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem shortestTree_finite_rank :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d),
  (shortestTree I allow w v).rank < (activeVertices I).length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.1.2.2.2

theorem shortestTree_finite_parent :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ) (hv : v ≠ I.source)
    (hd : (shortestTree I allow w v).distance = some d),
  ∃ u a, (shortestTree I allow w v).parent = some u ∧
      (shortestTree I allow w u).distance = some a ∧ d = a + w u v ∧
      (u,v) ∈ I.graph.edges ∧ allow u v = true ∧
      (shortestTree I allow w u).rank < (shortestTree I allow w v).rank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem shortestTree_source_zero :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v),
  (shortestTree I allow w I.source).distance = some 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.2.2.2.1

theorem shortestTree_path_bound :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P)
    (ha : P.IsChain (fun u v => allow u v = true)),
  ∃ d : ℝ, (shortestTree I allow (fun u v => w u v) t).distance = some d ∧
      d ≤ pathWeight w P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.1.1.2.1

theorem pathWeight_zero_chain :
  ∀ (w : ℕ → ℕ → ℝ≥0) (P : List ℕ)
    (h : pathWeight w P = 0),
  P.IsChain (fun u v => w u v = 0) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.1.1.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem firstPositiveLength_le_member :
  ∀ (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I),
  firstPositiveLength I ≤ x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.1.2.2.1

theorem member_le_largestLength :
  ∀ (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I),
  x ≤ largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.1.2.2.2

theorem largestLength_nonneg :
  ∀ (I : Instance),
  0 ≤ largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.1.1

theorem firstPositiveLength_le_largestLength :
  ∀ (I : Instance)
    (h : positiveLengths I ≠ []),
  firstPositiveLength I ≤ largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.1.2.1

theorem one_le_aspectRatio :
  ∀ (I : Instance),
  1 ≤ aspectRatio I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

theorem prepend_run :
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 31 = 1),
  Run input prependCmd s (prependResult s) 3 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.1.2.1

theorem storesList_cons :
  ∀ (mem : ℕ → ℕ) (base u : ℕ) (xs : List ℕ)
    (hb : 0 < base) (h : StoresList mem base xs),
  StoresList (Function.update mem (base - 1) u) (base - 1) (u :: xs) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.1.2.2

theorem storesList_map :
  ∀ (mem : ℕ → ℕ) (base : ℕ) (xs : List ℕ)
    (h : StoresList mem base xs),
  (List.range xs.length).map (fun k => mem (base + k)) = xs :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.2.1

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured

noncomputable def score (s : Store) (d : ℕ) : ℝ :=
  1 - s.rm (s.nr 50) + ∑ r ∈ Finset.range d, s.rr (current r)

noncomputable def scored (s : Store) (d : ℕ) : Store :=
  {s with rr := Function.update (Function.update s.rr 1 1) 0 (score s d)}

theorem add_terms (input : RAMInput) (rs : List ℕ) (s : Store) :
    evalAtoms input (rs.map (fun r => (⟨.realOp .add 0 0 (current r), trivial⟩ : Atom))) s =
      { s with rr := Function.update s.rr 0 (s.rr 0 + (rs.map (fun r => s.rr (current r))).sum) } := by
  induction rs generalizing s with
  | nil =>
    simp [evalAtoms]
  | cons r rs ih =>
    let t : Store := {s with rr := Function.update s.rr 0 (s.rr 0 + s.rr (current r))}
    have hcur (x : ℕ) : current x ≠ 0 := by unfold current; omega
    change evalAtoms input _ t = _
    rw [ih]
    simp [t, Function.update_of_ne (hcur _), Function.update_idem, add_assoc]

theorem list_sum_range (f : ℕ → ℝ) (d : ℕ) :
    ((List.range d).map f).sum = ∑ r ∈ Finset.range d, f r := by
  induction d with
  | zero => simp
  | succ d ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem score_run (input : RAMInput) (s : Store) (d : ℕ) :
    Run input (.atoms (scoreOps d)) s (scored s d) (3 + d) := by
  let t : Store := {s with rr := Function.update (Function.update s.rr 1 1) 0 (1 - s.rm (s.nr 50))}
  have hv : evalAtoms input (scoreOps d) s =
      evalAtoms input ((List.range d).map (fun r => (⟨.realOp .add 0 0 (current r), trivial⟩ : Atom))) t := by
    simp [t, scoreOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalReal,
      Function.update_idem]
  have h0 (r : ℕ) : current r ≠ 0 := by unfold current; omega
  have h1 (r : ℕ) : current r ≠ 1 := by unfold current; omega
  have he : evalAtoms input (scoreOps d) s = scored s d := by
    rw [hv, add_terms]
    simp [scored, score, t, Function.update_idem, Function.update_of_ne (h0 _),
      Function.update_of_ne (h1 _), list_sum_range]
  have hlen : (scoreOps d).length = 3 + d := by simp [scoreOps]; omega
  simpa only [he, hlen] using run_atoms input (scoreOps d) s

noncomputable def copied {α : Type} (d : ℕ) (reg : ℕ → α) (j : ℕ) : α := by
  classical
  exact if ∃ r < d, j = best r then reg (j - 1) else reg j

noncomputable def copies (d : ℕ) (s : Store) : Store :=
  {s with nr := copied d s.nr, rr := copied d s.rr}

theorem copy_succ {α : Type} (reg : ℕ → α) (d j : ℕ) :
    copied (d + 1) reg j = Function.update (copied d reg) (best d) (reg (current d)) j := by
  classical
  unfold copied
  by_cases hj : j = best d
  · subst j
    have h : ∃ r < d + 1, best d = best r := ⟨d, by omega, rfl⟩
    have hs : best d - 1 = current d := by unfold best current; omega
    rw [if_pos h, Function.update_self, hs]
  · have h : (∃ r < d + 1, j = best r) ↔ ∃ r < d, j = best r := by
      constructor
      · rintro ⟨r, hr, he⟩
        refine ⟨r, ?_, he⟩
        by_contra hn
        have eq : r = d := by omega
        exact hj (eq ▸ he)
      · rintro ⟨r, hr, he⟩; exact ⟨r, by omega, he⟩
    simp only [h, Function.update_of_ne hj]

theorem copies_zero (s : Store) : copies 0 s = s := by
  apply Store.ext
  · funext j; simp [copies, copied]
  · funext j; simp [copies, copied]
  · rfl
  · rfl

theorem copies_current (d r : ℕ) (s : Store) :
    (copies d s).nr (current r) = s.nr (current r) ∧
    (copies d s).rr (current r) = s.rr (current r) := by
  have h : ¬∃ j < d, current r = best j := by unfold current best; omega
  simp [copies, copied, h]

theorem copies_next (d : ℕ) (s : Store) :
    copies (d + 1) s = {copies d s with
      nr := Function.update (copies d s).nr (best d) (s.nr (current d)),
      rr := Function.update (copies d s).rr (best d) (s.rr (current d))} := by
  apply Store.ext
  · funext j; exact copy_succ s.nr d j
  · funext j; exact copy_succ s.rr d j
  · rfl
  · rfl

theorem save_lanes_run (input : RAMInput) (d : ℕ) (s : Store) :
    Run input (saveLanes d) s (copies d s) (2 * d) := by
  induction d with
  | zero => simpa only [saveLanes, copies_zero] using Run.skip (input := input) s
  | succ d ih =>
    let ops : List Atom := [⟨.realCopy (best d) (current d), trivial⟩, ⟨.natCopy (best d) (current d), trivial⟩]
    have he : evalAtoms input ops (copies d s) = copies (d + 1) s := by
      rw [copies_next]
      simp [ops, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, (copies_current d d s).1,
        (copies_current d d s).2]
    have hcost : 2 * d + ops.length = 2 * (d + 1) := by simp [ops]; omega
    exact hcost ▸ Run.seq ih (he ▸ run_atoms input ops (copies d s))

noncomputable def saved (s : Store) (d : ℕ) : Store :=
  copies d {s with
    nr := Function.update (Function.update s.nr 55 (s.nr 50)) 56 1
    rr := Function.update s.rr 3 (s.rr 0)}

theorem save_run (input : RAMInput) (s : Store) (d : ℕ) :
    Run input (saveCmd d) s (saved s d) (3 + 2 * d) := by
  exact Run.seq (run_atoms input saveHead s) (save_lanes_run input d _)

theorem consider_run (input : RAMInput) (s : Store) (d : ℕ) (hz : s.nr 30 = 0) :
    ∃ t steps, Run input (consider d) s t steps ∧
      t = (if s.nr 56 = 0 ∨ score s d < s.rr 3 then saved (scored s d) d else scored s d) ∧
      steps ≤ 3 * d + 10 := by
  let v := scored s d
  have h := score_run input s d
  by_cases hnone : s.nr 56 = 0
  · have hg : (Guard.nat .eq 56 30).eval v = true := by simp [v, scored, Guard.eval, natTest, hnone, hz]
    exact ⟨_, _, Run.seq h (Run.branchTrue hg (save_run input v d)), by simp [hnone, v], by omega⟩
  · have hg : (Guard.nat .eq 56 30).eval v = false := by simp [v, scored, Guard.eval, natTest, hnone, hz]
    by_cases hlt : score s d < s.rr 3
    · have hr : (Guard.real .lt 0 3).eval v = true := by simp [v, scored, Guard.eval, realTest, hlt]
      exact ⟨_, _, Run.seq h (Run.branchFalse hg (Run.branchTrue hr (save_run input v d))),
        by simp [hlt, v], by omega⟩
    · have hr : (Guard.real .lt 0 3).eval v = false := by simp [v, scored, Guard.eval, realTest, hlt]
      exact ⟨_, _, Run.seq h (Run.branchFalse hg (Run.branchFalse hr (Run.skip v))),
        by simp [hnone, hlt, v], by omega⟩

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement

theorem ticks_pos (k : ℕ) (δ : ℝ) (hk : 0 < k) (hδ : 0 < δ) :
    0 < ticks k δ := by
  unfold ticks
  apply Nat.ceil_pos.mpr
  positivity

theorem ticks_sufficient (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    512 * (k : ℝ) ≤ (ticks k δ : ℝ) * δ ^ 2 := by
  exact (div_le_iff₀ (sq_pos_of_pos hδ)).mp (Nat.le_ceil _)

theorem clockCoordinates_length_le {k : ℕ} (I : MultiInstance k) :
    (clockCoordinates I).length ≤ k := by
  simpa [clockCoordinates] using
    List.length_filter_le (fun r : Fin k => r.val = 0 ∨ 0 < coordinateBudget I 1 r)
      (List.finRange k)

theorem clockCoordinates_mem {k : ℕ} (I : MultiInstance k) (r : Fin k) :
    r ∈ clockCoordinates I ↔ r.val = 0 ∨ 0 < coordinateBudget I 1 r := by
  simp [clockCoordinates]

theorem clockCoordinates_pos {k : ℕ} (I : MultiInstance k) (hk : 0 < k) :
    0 < (clockCoordinates I).length := by
  have hm : (⟨0, hk⟩ : Fin k) ∈ clockCoordinates I :=
    (clockCoordinates_mem I _).mpr (Or.inl rfl)
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hm)

theorem clockBudget_pos {k : ℕ} (I : MultiInstance k) (L : ℝ) (hL : 0 < L)
    (r : Fin (clockCoordinates I).length) :
    0 < coordinateBudget I L ((clockCoordinates I).get r) := by
  have hm := (clockCoordinates_mem I _).mp (List.get_mem _ r)
  unfold coordinateBudget at hm ⊢
  split_ifs with h
  · exact hL
  · rcases hm with h' | h'
    · exact (h h').elim
    · simpa only [dif_neg h] using h'

theorem clockMean_nonneg {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (r : Fin A.d) (u v : ℕ) : 0 ≤ clockMean A r u v := by
  have hB := clockBudget_pos A.I A.L hL r
  unfold clockMean clockRate
  apply mul_nonneg
  · apply div_nonneg (Nat.cast_nonneg _)
    exact mul_nonneg (by linarith) hB.le
  · exact (coordinateWeight A.I (A.coords.get r) u v).coe_nonneg

theorem clockPGF_pos {k : ℕ} (A : ClockCall k) (r : Fin A.d) (u v : ℕ) :
    0 < clockPGF A r u v := Real.exp_pos _

theorem clockZ_pos {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) : 0 < clockZ A := by
  unfold clockZ
  apply div_pos <;> linarith

theorem clockZ_lt_one {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) : clockZ A < 1 := by
  unfold clockZ
  apply (div_lt_one (by linarith : 0 < 1 + A.δ)).mpr
  linarith

theorem length_vectors (d q : ℕ) : (vectors d q).length = q ^ d := by
  induction d with
  | zero => simp [vectors]
  | succ d ih =>
    simp [vectors, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

theorem mem_vectors {d q : ℕ} (i : Fin d → ℕ) :
    i ∈ vectors d q ↔ ∀ r, i r < q := by
  induction d with
  | zero =>
    have h : i = fun r => Fin.elim0 r := Subsingleton.elim _ _
    simp [vectors, h]
  | succ d ih =>
    constructor
    · intro h
      obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp h
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
      subst i
      intro r
      refine Fin.cases ?_ (fun s => ?_) r
      · simpa using List.mem_range.mp ha
      · simpa using (ih j).mp hj s
    · intro h
      apply List.mem_flatMap.mpr
      refine ⟨i 0, List.mem_range.mpr (h 0), ?_⟩
      apply List.mem_map.mpr
      refine ⟨Fin.tail i, (ih _).mpr (fun r => h r.succ), ?_⟩
      exact Fin.cons_self_tail i

theorem vectors_nodup (d q : ℕ) : (vectors d q).Nodup := by
  induction d with
  | zero => simp [vectors]
  | succ d ih =>
    rw [vectors, List.nodup_flatMap]
    constructor
    · intro a ha
      exact ih.map (Fin.cons_right_injective (α := fun _ => ℕ) a)
    · apply (List.nodup_range (n := q)).imp
      intro a b hab i hi hj
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hj
      exact hab (congrArg (fun v : Fin (d + 1) → ℕ => v 0) he).symm

theorem rectangle_mem {k : ℕ} (A : ClockCall k) (i a : Fin A.d → ℕ) :
    a ∈ rectangle A i ↔ ∀ r, i r + a r < A.q := by
  classical
  simp only [rectangle, List.mem_filter, decide_eq_true_eq, mem_vectors]
  constructor
  · exact And.right
  · intro h
    exact ⟨fun r => (Nat.le_add_left _ _).trans_lt (h r), h⟩

theorem rectangle_nodup {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) :
    (rectangle A i).Nodup := (vectors_nodup _ _).filter _

theorem rectangle_zero_mem {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (hi : ∀ r, i r < A.q) : (fun _ => 0) ∈ rectangle A i := by
  exact (rectangle_mem A i _).mpr (by simpa)

theorem rectangle_ne_nil {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (hi : ∀ r, i r < A.q) : rectangle A i ≠ [] :=
  List.ne_nil_of_mem (rectangle_zero_mem A i hi)

theorem vectorIndex_cons {d : ℕ} (q a : ℕ) (i : Fin d → ℕ) :
    vectorIndex q (Fin.cons a i) = a * q ^ d + vectorIndex q i := by
  unfold vectorIndex
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel,
    Fin.cons_succ, Fin.val_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  omega

theorem vectorIndex_lt {d q : ℕ} (i : Fin d → ℕ) (hi : ∀ r, i r < q) :
    vectorIndex q i < q ^ d := by
  induction d with
  | zero => simp [vectorIndex]
  | succ d ih =>
    have ht := ih (Fin.tail i) (fun r => hi r.succ)
    have h0 := hi 0
    conv_lhs => rw [← Fin.cons_self_tail i]
    rw [vectorIndex_cons, pow_succ]
    have hmul := Nat.mul_le_mul_right (q ^ d) (Nat.succ_le_of_lt h0)
    nlinarith

theorem vectorIndex_le {d q : ℕ} (i j : Fin d → ℕ) (h : ∀ r, i r ≤ j r) :
    vectorIndex q i ≤ vectorIndex q j := by
  exact Finset.sum_le_sum (fun r _ => Nat.mul_le_mul_right _ (h r))

theorem vectorIndex_lt_of_le {d q : ℕ} (hq : 0 < q) (i j : Fin d → ℕ)
    (h : ∀ r, i r ≤ j r) (hne : i ≠ j) : vectorIndex q i < vectorIndex q j := by
  classical
  have hex : ∃ r, i r ≠ j r := by
    by_contra hn
    exact hne (funext (fun r => by simpa using not_exists.mp hn r))
  obtain ⟨r, hr⟩ := hex
  apply Finset.sum_lt_sum (fun s _ => Nat.mul_le_mul_right _ (h s))
  refine ⟨r, Finset.mem_univ _, ?_⟩
  exact Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne (h r) hr) (pow_pos hq _)

theorem put_same {d : ℕ} (T : MultiTable d) (v : ℕ) (i : Fin d → ℕ) (c : MultiCell) :
    put T v i c v i = c := by simp [put]

theorem put_other {d : ℕ} (T : MultiTable d) (v w : ℕ) (i j : Fin d → ℕ)
    (c : MultiCell) (h : w ≠ v ∨ j ≠ i) : put T v i c w j = T w j := by
  simp only [put]
  exact if_neg (by tauto)

theorem value_of_valid {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) :
    value A T v i = (T v i).value := by
  simp only [value]
  exact if_neg (by simpa using hi)

theorem value_of_saturated {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) (hi : ∃ r, A.q ≤ i r) :
    value A T v i = 1 := by simp [value, hi]

theorem incrementMass_nonneg {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (u v : ℕ) (a : Fin A.d → ℕ) :
    0 ≤ incrementMass A u v a := by
  apply Finset.prod_nonneg
  intro r hr
  unfold ActuarialValuation.poissonCountMass
  have hm := clockMean_nonneg A hδ hL r u v
  positivity

theorem selectMin_fold_mem {α : Type} (f : α → ℝ) (xs : List α) (a : α) :
    xs.foldl (fun x y => if f y < f x then y else x) a ∈ a :: xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split_ifs with h
    · have hm := ih x
      simp only [List.mem_cons] at hm ⊢
      tauto
    · have hm := ih a
      simp only [List.mem_cons] at hm ⊢
      tauto

theorem selectMin_mem {α : Type} (f : α → ℝ) (xs : List α) (a : α) (h : xs ≠ []) :
    selectMin f xs a ∈ xs := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs =>
    simpa [selectMin, List.foldl_cons] using selectMin_fold_mem f xs x

theorem selectMin_fold_le {α : Type} (f : α → ℝ) (xs : List α) (a : α) :
    f (xs.foldl (fun x y => if f y < f x then y else x) a) ≤ f a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split_ifs with h
    · exact (ih x).trans h.le
    · exact ih a

theorem selectMin_fold_le_mem {α : Type} (f : α → ℝ) (xs : List α) (a b : α)
    (hb : b ∈ xs) : f (xs.foldl (fun x y => if f y < f x then y else x) a) ≤ f b := by
  induction xs generalizing a with
  | nil => simp at hb
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · split_ifs with h
      · exact selectMin_fold_le f xs b
      · exact (selectMin_fold_le f xs a).trans (le_of_not_gt h)
    · exact ih _ hb

theorem selectMin_le_mem {α : Type} (f : α → ℝ) (xs : List α) (a b : α)
    (hb : b ∈ xs) : f (selectMin f xs a) ≤ f b :=
  selectMin_fold_le_mem f xs (xs.headD a) b hb

theorem incident_source_mem {k : ℕ} (I : MultiInstance k) :
    I.source ∈ incidentVertices I := by simp [incidentVertices]

theorem incident_valid {k : ℕ} (I : MultiInstance k) (v : ℕ)
    (hv : v ∈ incidentVertices I) : v < I.graph.n := by
  simp only [incidentVertices, List.mem_eraseDups, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact I.source_valid
  · obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    have hb := I.graph.endpoints e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hb.1
    · exact hb.2

theorem selectedBranch_source {k : ℕ} (I : MultiInstance k) (ε : ℝ) :
    selectedBranch I ε I.source = .source := by simp [selectedBranch]

theorem selectedDistance_source {k : ℕ} (I : MultiInstance k) (ε : ℝ) :
    selectedDistance I ε I.source = some 0 := by
  simp [selectedDistance, selectedBranch_source]

theorem selectedPath_source {k : ℕ} (I : MultiInstance k) (ε : ℝ) :
    selectedPath I ε I.source = some [I.source] := by
  simp [selectedPath, selectedBranch_source]

theorem source_relaxed {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 ≤ ε) :
    RelaxedPath I ε I.source [I.source] := by
  constructor
  · simp [IsPath]
  · intro r
    simp only [pathWeight, List.tail_cons, List.zip_nil_right, List.map_nil, List.sum_nil]
    exact mul_nonneg (by linarith) (I.budget r).coe_nonneg

theorem selectedDistance_none_iff {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ) :
    selectedDistance I ε t = none ↔ selectedBranch I ε t = .absent := by
  classical
  unfold selectedDistance
  generalize hb : selectedBranch I ε t = b
  cases b with
  | absent => simp
  | source => simp
  | ordinary =>
    have hh : ((shortestTree I t).distance).isSome = true := by
      unfold selectedBranch at hb
      split at hb
      · cases hb
      · split at hb
        · split at hb <;> cases hb
        · split at hb
          · assumption
          · cases hb
    simp only [Option.isSome_iff_ne_none] at hh
    simp [hh]
  | table r =>
    have hh : ∃ A, (outerCalls I ε)[r]? = some A := by
      unfold selectedBranch at hb
      split at hb
      · cases hb
      · split at hb
        · split at hb
          · cases hb
          · rename_i j hj
            have he : j = r := by simpa using hb
            subst j
            have hm := List.mem_of_find?_eq_some hj
            have hr := List.mem_range.mp hm
            exact ⟨(outerCalls I ε)[r], List.getElem?_eq_getElem hr⟩
        · split at hb <;> cases hb
    obtain ⟨A, hA⟩ := hh
    simp [hA]

theorem encoded_distance {k : ℕ} (I : MultiInstance k) (ε : ℝ) (S : RAMState)
    (h : EncodesMultiOutput I ε S) (t : ℕ) (ht : t < I.graph.n) :
    multiDistance S t = selectedDistance I ε t := by
  obtain ⟨hq, hs, hn, hk, hd, hc, hz, hH, hcoords, htargets, hrest⟩ := h
  obtain ⟨htag, hdist, hcall⟩ := htargets t ht
  unfold multiDistance
  rw [hk, htag]
  cases he : selectedDistance I ε t with
  | none =>
    have hb := (selectedDistance_none_iff I ε t).mp he
    simp [hb, outputTag]
  | some d =>
    have hb : selectedBranch I ε t ≠ .absent := by
      intro hb
      have hn := (selectedDistance_none_iff I ε t).mpr hb
      rw [he] at hn
      cases hn
    have htag' : outputTag (selectedBranch I ε t) ≠ 0 := by
      cases hh : selectedBranch I ε t <;> simp_all [outputTag]
    simp [htag', hdist d he]

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem range_blocks (rows width : ℕ) :
    (List.range rows).flatMap (fun r => (List.range width).map (r * width + ·)) =
      List.range (rows * width) := by
  induction rows with
  | zero => simp
  | succ rows ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add]
    simp

theorem vectorIndices_in_order (d q : ℕ) :
    ((vectors d q).map (vectorIndex q)) = List.range (q ^ d) := by
  induction d with
  | zero => simp [vectors, vectorIndex, List.range_one]
  | succ d ih =>
    rw [vectors, List.map_flatMap]
    have he (a : ℕ) : (((vectors d q).map (Fin.cons a)).map (vectorIndex q)) =
        (List.range (q ^ d)).map (a * q ^ d + ·) := by
      rw [← ih]
      simp only [List.map_map, Function.comp_def, vectorIndex_cons]
    simp only [he, pow_succ', range_blocks]

theorem vectorIndex_add {d : ℕ} (q : ℕ) (i a : Fin d → ℕ) :
    vectorIndex q (fun r => i r + a r) = vectorIndex q i + vectorIndex q a := by
  simp only [vectorIndex, Nat.add_mul, Finset.sum_add_distrib]

theorem scanAddress_add {d : ℕ} (base n q v : ℕ) (i a : Fin d → ℕ) :
    scanAddress base n q v (fun r => i r + a r) =
      scanAddress base n q v i + vectorIndex q a * ((d + 4) * n) := by
  simp only [scanAddress, vectorIndex_add]
  ring

theorem scanAddress_order {d : ℕ} (base n q v : ℕ) (i : Fin d → ℕ) :
    (vectors d q).map (fun a => scanAddress base n q v (fun r => i r + a r)) =
      (List.range (q ^ d)).map (fun j => scanAddress base n q v i + j * ((d + 4) * n)) := by
  rw [← vectorIndices_in_order d q]
  simp only [List.map_map, Function.comp_def, scanAddress_add]

noncomputable def keepCandidate {α : Type} (f : α → ℝ) (old : Option α) (a : α) : Option α :=
  match old with
  | none => some a
  | some b => some (if f a < f b then a else b)

theorem fold_candidates_some {α : Type} (f : α → ℝ) (xs : List α) (b : α) :
    xs.foldl (keepCandidate f) (some b) =
      some (xs.foldl (fun w a => if f a < f w then a else w) b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => simpa only [List.foldl_cons, keepCandidate] using ih (if f a < f b then a else b)

theorem candidate_choice {α : Type} (f : α → ℝ) (a : α) (xs : List α) :
    (a :: xs).foldl (keepCandidate f) none = some (selectMin f (a :: xs) a) := by
  simp [selectMin, List.foldl_cons, keepCandidate, fold_candidates_some]

theorem rectangle_scan_choice {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (f : (Fin A.d → ℕ) → ℝ) (a : Fin A.d → ℕ) (rest : List (Fin A.d → ℕ))
    (hr : rectangle A i = a :: rest) :
    (vectors A.d A.q).foldl (fun b v => if ∀ r, i r + v r < A.q then keepCandidate f b v else b) none =
      some (selectMin f (a :: rest) a) := by
  calc
    _ = (rectangle A i).foldl (keepCandidate f) none := by
      simp only [rectangle, List.foldl_filter, decide_eq_true_eq]
    _ = _ := by rw [hr]; exact candidate_choice f a rest

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured

theorem copied_best {α : Type} (f : ℕ → α) (d r : ℕ) (hr : r < d) :
    copied d f (best r) = f (current r) := by
  have h : ∃ j < d, best r = best j := ⟨r, hr, rfl⟩
  have he : best r - 1 = current r := by unfold best current; omega
  simp [copied, h, he]

theorem copied_small {α : Type} (f : ℕ → α) (d j : ℕ) (hj : j < 100) :
    copied d f j = f j := by
  have h : ¬∃ r < d, j = best r := by unfold best; omega
  simp [copied, h]

theorem saved_fields (d : ℕ) (s : Store) :
    let t := saved (scored s d) d
    t.nr 55 = s.nr 50 ∧ t.nr 56 = 1 ∧ t.rr 3 = score s d ∧
      ∀ r < d, t.nr (best r) = s.nr (current r) ∧ t.rr (best r) = s.rr (current r) := by
  dsimp only
  have h1 {r : ℕ} : current r ≠ 1 := by unfold current; omega
  have h0 {r : ℕ} : current r ≠ 0 := by unfold current; omega
  have h3 {r : ℕ} : current r ≠ 3 := by unfold current; omega
  have h55 {r : ℕ} : current r ≠ 55 := by unfold current; omega
  have h56 {r : ℕ} : current r ≠ 56 := by unfold current; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [saved, scored, copies, copied_small _ _ _ (by decide : 55 < 100)]
  · simp [saved, scored, copies, copied_small _ _ _ (by decide : 56 < 100)]
  · simp [saved, scored, copies, copied_small _ _ _ (by decide : 3 < 100)]
  · intro r hr
    simp [saved, scored, copies, copied_best _ d r hr, Function.update_of_ne h0,
      Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h55, Function.update_of_ne h56]

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured

def within (d : ℕ) (s : Store) := ∀ r < d, s.nr (current r) < s.nr 57

theorem guards_true {input : RAMInput} {c : Cmd} {s t : Store} {steps : ℕ}
    (d : ℕ) (hv : within d s) (hr : Run input c s t steps) :
    Run input (guardCounts c d) s t (2 * d + steps) := by
  induction d with
  | zero => simpa [guardCounts] using hr
  | succ n ih =>
    have hg : (Guard.nat .lt (current n) 57).eval s = true := by
      simp [Guard.eval, natTest, hv n (by omega)]
    have hh := Run.branchTrue (b := Cmd.skip) hg (ih (fun r hr => hv r (by omega)))
    simpa only [guardCounts, show 1 + (2 * n + steps) + 1 = 2 * (n + 1) + steps by omega] using hh

theorem guards_false (input : RAMInput) (c : Cmd) (s : Store) (d : ℕ) (hv : ¬within d s) :
    ∃ cost, Run input (guardCounts c d) s s cost ∧ cost ≤ 2 * d := by
  induction d with
  | zero => exact (hv (fun _ hr => by omega)).elim
  | succ n ih =>
    by_cases hh : s.nr (current n) < s.nr 57
    · have hprev : ¬within n s := by
        intro hw
        apply hv
        intro r hr
        by_cases he : r = n
        · simpa [he] using hh
        · exact hw r (by omega)
      obtain ⟨cost, hc, hn⟩ := ih hprev
      have hg : (Guard.nat .lt (current n) 57).eval s = true := by simp [Guard.eval, natTest, hh]
      exact ⟨_, Run.branchTrue hg hc, by omega⟩
    · have hg : (Guard.nat .lt (current n) 57).eval s = false := by simp [Guard.eval, natTest, hh]
      exact ⟨_, Run.branchFalse hg (Run.skip s), by omega⟩

def advanced (s : Store) : Store := {s with nr := Function.update s.nr 50 (s.nr 50 + s.nr 59)}

noncomputable def considered (s : Store) (d : ℕ) : Store :=
  if s.nr 56 = 0 ∨ score s d < s.rr 3 then saved (scored s d) d else scored s d

noncomputable def visited (s : Store) (d : ℕ) : Store := by
  classical
  exact advanced (if within d s then considered s d else s)

theorem visit_run (input : RAMInput) (d : ℕ) (s : Store) (hz : s.nr 30 = 0) :
    ∃ cost, Run input (visit d) s (visited s d) cost ∧ cost ≤ 5 * d + 11 := by
  classical
  by_cases hv : within d s
  · obtain ⟨w, steps, hc, he, hn⟩ := consider_run input s d hz
    have he' : w = considered s d := he
    subst w
    have ha : Run input (.atom advanceCell) (considered s d) (visited s d) 1 := by
      rw [visited, if_pos hv]
      exact Run.atom advanceCell _
    exact ⟨_, Run.seq (guards_true d hv hc) ha, by omega⟩
  · obtain ⟨steps, hrun, hn⟩ := guards_false input (consider d) s d hv
    have ha : Run input (.atom advanceCell) s (visited s d) 1 := by
      rw [visited, if_neg hv]
      exact Run.atom advanceCell _
    exact ⟨_, Run.seq hrun ha, by omega⟩

theorem copied_other {α : Type} (f : ℕ → α) (d j : ℕ) (h : ∀ r < d, j ≠ best r) :
    copied d f j = f j := by
  have hn : ¬∃ r < d, j = best r := by simpa only [not_exists, not_and] using h
  simp only [copied, if_neg hn]

theorem considered_nat (s : Store) (d j : ℕ) (h : ∀ r < d, j ≠ best r)
    (h55 : j ≠ 55) (h56 : j ≠ 56) : (considered s d).nr j = s.nr j := by
  unfold considered
  split
  · simp [saved, copies, scored, copied_other _ d j h, Function.update_of_ne h55, Function.update_of_ne h56]
  · rfl

theorem considered_real (s : Store) (d j : ℕ) (h : ∀ r < d, j ≠ best r)
    (h0 : j ≠ 0) (h1 : j ≠ 1) (h3 : j ≠ 3) : (considered s d).rr j = s.rr j := by
  unfold considered
  split
  · simp [saved, copies, scored, copied_other _ d j h, Function.update_of_ne h0,
      Function.update_of_ne h1, Function.update_of_ne h3]
  · simp [scored, Function.update_of_ne h0, Function.update_of_ne h1]

theorem visit_frame (s : Store) (d : ℕ) :
    (visited s d).nr 50 = s.nr 50 + s.nr 59 ∧ (visited s d).nm = s.nm ∧ (visited s d).rm = s.rm ∧
      (∀ j, (∀ r < d, j ≠ best r) → j ≠ 50 → j ≠ 55 → j ≠ 56 → (visited s d).nr j = s.nr j) ∧
      (∀ j, (∀ r < d, j ≠ best r) → j ≠ 0 → j ≠ 1 → j ≠ 3 → (visited s d).rr j = s.rr j) := by
  classical
  unfold visited
  by_cases hv : within d s
  · rw [if_pos hv]
    have h50 : (considered s d).nr 50 = s.nr 50 :=
      considered_nat s d 50 (fun r _ => by unfold best; omega) (by decide) (by decide)
    have h59 : (considered s d).nr 59 = s.nr 59 :=
      considered_nat s d 59 (fun r _ => by unfold best; omega) (by decide) (by decide)
    have hm : (considered s d).nm = s.nm ∧ (considered s d).rm = s.rm := by
      unfold considered; split <;> exact ⟨rfl, rfl⟩
    refine ⟨by simp [advanced, h50, h59], hm.1, hm.2, ?_, ?_⟩
    · intro j hj hn h55 h56
      simpa [advanced, Function.update_of_ne hn] using considered_nat s d j hj h55 h56
    · exact considered_real s d
  · rw [if_neg hv]
    exact ⟨by simp [advanced], rfl, rfl, fun j _ h50 _ _ => Function.update_of_ne h50 _ _,
      fun _ _ _ _ _ => rfl⟩

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option Elab.async false
open scoped NNReal BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem product_hasSum {d : ℕ} (f : Fin d → ℕ → ℝ) (s : Fin d → ℝ)
    (hf : ∀ r, HasSum (f r) (s r)) (hf0 : ∀ r a, 0 ≤ f r a) :
    HasSum (fun a : Fin d → ℕ => ∏ r, f r (a r)) (∏ r, s r) := by
  induction d with
  | zero =>
    letI : Fintype (Fin 0 → ℕ) := Fintype.ofSubsingleton (fun _ => 0)
    simpa using (hasSum_fintype (fun a : Fin 0 → ℕ => ∏ r, f r (a r)))
  | succ d ih =>
    have ht := ih (fun r => f r.succ) (fun r => s r.succ)
      (fun r => hf r.succ) (fun r => hf0 r.succ)
    have hp := (hf 0).mul ht
      ((hf 0).summable.mul_of_nonneg ht.summable (hf0 0)
        (fun a => Finset.prod_nonneg (fun r _ => hf0 r.succ (a r))))
    apply (Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv] using hp

theorem product_weighted_hasSum {d : ℕ} (f : Fin d → ℕ → ℝ)
    (hf : ∀ r, HasSum (f r) 1) (hf0 : ∀ r a, 0 ≤ f r a)
    (j : Fin d) (g : ℕ → ℝ) (G : ℝ) (hg0 : ∀ a, 0 ≤ g a)
    (hg : HasSum (fun a => f j a * g a) G) :
    HasSum (fun a : Fin d → ℕ => (∏ r, f r (a r)) * g (a j)) G := by
  classical
  let h : Fin d → ℕ → ℝ := fun r a => f r a * (if r = j then g a else 1)
  have hh : ∀ r, HasSum (h r) (if r = j then G else 1) := by
    intro r
    by_cases hr : r = j
    · subst r
      simpa [h] using hg
    · simpa [h, hr] using hf r
  have hh0 : ∀ r a, 0 ≤ h r a := by
    intro r a
    apply mul_nonneg (hf0 r a)
    split_ifs
    · exact hg0 a
    · norm_num
  have hs := product_hasSum h (fun r => if r = j then G else 1) hh hh0
  have hprod (a : Fin d → ℕ) : (∏ r, h r (a r)) = (∏ r, f r (a r)) * g (a j) := by
    dsimp only [h]
    rw [Finset.prod_mul_distrib]
    congr 1
    simp
  have hc : (∏ r : Fin d, if r = j then G else 1) = G := by simp
  rw [hc] at hs
  simpa only [hprod] using hs

theorem incrementMass_hasSum {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (u v : ℕ) :
    HasSum (fun a : Fin A.d → ℕ => incrementMass A u v a) (1 : ℝ) := by
  unfold incrementMass
  have hf : ∀ r : Fin A.d, HasSum (ActuarialValuation.poissonCountMass (clockMean A r u v)) (1 : ℝ) :=
    fun r => RSP.PoissonBridge.poissonCountMass_hasSum _ (clockMean_nonneg A hδ hL r u v)
  have hf0 : ∀ (r : Fin A.d) (a : ℕ), 0 ≤ ActuarialValuation.poissonCountMass (clockMean A r u v) a :=
    fun r a => RSP.PoissonBridge.poissonCountMass_nonneg _ (clockMean_nonneg A hδ hL r u v) a
  have h := product_hasSum (d := A.d)
    (fun r : Fin A.d => ActuarialValuation.poissonCountMass (clockMean A r u v))
    (fun _ : Fin A.d => (1 : ℝ)) hf hf0
  simpa only [Finset.prod_const_one] using h

theorem rectangle_mass_le_one {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (u v : ℕ) (i : Fin A.d → ℕ) :
    ((rectangle A i).map (incrementMass A u v)).sum ≤ 1 := by
  classical
  have hp := incrementMass_hasSum A hδ hL u v
  have hh := sum_le_hasSum (rectangle A i).toFinset
    (fun a ha => incrementMass_nonneg A hδ hL u v a) hp
  simpa only [List.sum_toFinset _ (rectangle_nodup A i)] using hh

theorem incrementMass_pgf_hasSum {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (u v : ℕ) (j : Fin A.d) :
    HasSum (fun a => incrementMass A u v a * clockZ A ^ a j) (clockPGF A j u v) := by
  have hg := RSP.Tails.poisson_pgf_hasSum
    ⟨clockMean A j u v, clockMean_nonneg A hδ hL j u v⟩ (clockZ A)
  have hg' : HasSum (fun a => ActuarialValuation.poissonCountMass (clockMean A j u v) a *
      clockZ A ^ a) (clockPGF A j u v) := by
    exact hg
  exact product_weighted_hasSum
    (fun r => ActuarialValuation.poissonCountMass (clockMean A r u v))
    (fun r => RSP.PoissonBridge.poissonCountMass_hasSum _ (clockMean_nonneg A hδ hL r u v))
    (fun r => RSP.PoissonBridge.poissonCountMass_nonneg _ (clockMean_nonneg A hδ hL r u v))
    j (fun a => clockZ A ^ a) (clockPGF A j u v)
    (fun a => pow_nonneg (clockZ_pos A hδ).le a) hg'

def MultiRange {d : ℕ} (T : MultiTable d) : Prop :=
  ∀ v i, 0 ≤ (T v i).value ∧ (T v i).value ≤ 1

theorem value_range {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (hT : MultiRange T) (v : ℕ) (i : Fin A.d → ℕ) :
    0 ≤ value A T v i ∧ value A T v i ≤ 1 := by
  unfold value
  split_ifs
  · norm_num
  · exact hT v i

theorem expectation_range {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d) (hT : MultiRange T)
    (u v : ℕ) (i : Fin A.d → ℕ) :
    0 ≤ expectation A T u v i ∧ expectation A T u v i ≤ 1 := by
  have hm := rectangle_mass_le_one A hδ hL u v i
  have hsum0 : 0 ≤ ((rectangle A i).map (fun a => incrementMass A u v a *
      value A T u (fun r => i r + a r))).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (incrementMass_nonneg A hδ hL u v a) (value_range A T hT _ _).1
  have hsum1 : ((rectangle A i).map (fun a => incrementMass A u v a *
      value A T u (fun r => i r + a r))).sum ≤
      ((rectangle A i).map (incrementMass A u v)).sum := by
    apply List.sum_le_sum
    intro a ha
    exact mul_le_of_le_one_right (incrementMass_nonneg A hδ hL u v a)
      (value_range A T hT _ _).2
  unfold expectation
  constructor <;> dsimp only <;> linarith

noncomputable def quadratic (q M i r : ℝ) : ℝ :=
  (r + (i + r - M) ^ 2) / (q - M) ^ 2

theorem quadratic_nonneg (q M i r : ℝ) (hr : 0 ≤ r) :
    0 ≤ quadratic q M i r := by unfold quadratic; positivity

theorem quadratic_saturated (q M i r : ℝ) (hM : M < q)
    (hi : q ≤ i) (hr : 0 ≤ r) : 1 ≤ quadratic q M i r := by
  unfold quadratic
  apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hM))).mpr
  have hx : 0 ≤ i + r - q := by linarith
  nlinarith [sq_nonneg (i + r - q), mul_nonneg (sub_nonneg.mpr hM.le) hx]

theorem quadratic_initial (q M : ℝ) : quadratic q M 0 M = M / (q - M) ^ 2 := by
  simp [quadratic]

theorem quadratic_hasSum (q M i r : ℝ) (e : ℝ≥0) :
    HasSum (fun a : ℕ => RSP.Tails.mass e a * quadratic q M (i + a) r)
      (quadratic q M i (r + e)) := by
  have h := ((RSP.Tails.secondMoment_hasSum e).add
    ((RSP.Tails.firstMoment_hasSum e).mul_right (2 * (i + r - M)))).add
      ((RSP.Tails.mass_hasSum e).mul_right (r + (i + r - M) ^ 2))
  convert! h.div_const ((q - M) ^ 2) using 1
  · ext a
    unfold quadratic
    ring
  · unfold quadratic
    ring

theorem quadratic_vector_hasSum {d : ℕ} (q : ℝ) (M i r : Fin d → ℝ)
    (e : Fin d → ℝ≥0) (hr : ∀ j, 0 ≤ r j) :
    HasSum (fun a : Fin d → ℕ =>
      (∏ j, RSP.Tails.mass (e j) (a j)) *
        ∑ j, quadratic q (M j) (i j + a j) (r j))
      (∑ j, quadratic q (M j) (i j) (r j + e j)) := by
  have h (j : Fin d) := product_weighted_hasSum
    (fun j => RSP.Tails.mass (e j)) (fun j => RSP.Tails.mass_hasSum (e j))
    (fun j => RSP.Tails.mass_nonneg (e j)) j
    (fun a => quadratic q (M j) (i j + a) (r j))
    (quadratic q (M j) (i j) (r j + e j))
    (fun a => quadratic_nonneg q (M j) (i j + a) (r j) (hr j))
    (quadratic_hasSum q (M j) (i j) (r j) (e j))
  simpa only [Finset.mul_sum] using (hasSum_sum (s := Finset.univ) (fun j _ => h j))

theorem rectangle_comparison {α : Type*} (R : Finset α) (p D G : α → ℝ) (bound : ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp : HasSum p 1)
    (hG : HasSum (fun a => p a * G a) bound)
    (hin : ∀ a ∈ R, D a ≤ G a) (hout : ∀ a ∉ R, 1 ≤ G a) :
    1 - ∑ a ∈ R, p a + ∑ a ∈ R, p a * D a ≤ bound := by
  classical
  let correction := fun a => if a ∈ R then p a * (1 - D a) else 0
  have hc : HasSum correction (∑ a ∈ R, p a * (1 - D a)) := by
    have hc0 : HasSum correction (∑ a ∈ R, correction a) :=
      hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional α)
        (s := R) (f := correction) (fun a ha => by simp [correction, ha])
    simpa [correction] using hc0
  have hsum := hG.add hc
  have hle : 1 ≤ bound + ∑ a ∈ R, p a * (1 - D a) := by
    apply hasSum_le _ hp hsum
    intro a
    by_cases ha : a ∈ R
    · dsimp [correction]
      rw [if_pos ha]
      nlinarith [mul_le_mul_of_nonneg_left (hin a ha) (hp0 a)]
    · dsimp [correction]
      rw [if_neg ha]
      nlinarith [mul_le_mul_of_nonneg_left (hout a ha) (hp0 a)]
  have hid : (∑ a ∈ R, p a * (1 - D a)) =
      (∑ a ∈ R, p a) - ∑ a ∈ R, p a * D a := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hid] at hle
  linarith

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement

theorem fold_preserves {α β : Type*} (f : β → α → β) (P : β → Prop)
    (xs : List α) (b : β) (hb : P b)
    (hf : ∀ a ∈ xs, ∀ b, P b → P (f b a)) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
    apply ih (f b a) (hf a (by simp) b hb)
    intro c hc U hU
    exact hf c (by simp [hc]) U hU

def LayerRange {d : ℕ} (S : MultiLayer d) : Prop :=
  MultiRange S.table ∧ ∀ v, 0 ≤ S.keys v ∧ S.keys v ≤ 1

noncomputable def settle {d : ℕ} (S : MultiLayer d) (u : ℕ) (i : Fin d → ℕ) : MultiLayer d :=
  { S with
    table := put S.table u i ⟨S.keys u, S.parents u, S.nextRank⟩
    queue := S.queue.erase u
    nextRank := S.nextRank + 1 }

noncomputable def relaxAll {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (u : ℕ) (S : MultiLayer A.d) : MultiLayer A.d :=
  (callEdges A).foldl (relax A i u) S

noncomputable def picked {k : ℕ} (A : ClockCall k) (S : MultiLayer A.d) : ℕ :=
  selectMin S.keys S.queue A.I.source

noncomputable def runQueue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : MultiLayer A.d :=
  (List.range n).foldl (fun S _ => pop A i S) S

theorem runQueue_zero {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : runQueue A i 0 S = S := rfl

theorem runQueue_succ {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : runQueue A i (n + 1) S = pop A i (runQueue A i n S) := by
  simp [runQueue, List.range_succ, List.foldl_append]

theorem relax_table {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : (relax A i u S e).table = S.table := by
  unfold relax
  dsimp only
  split_ifs <;> rfl

theorem relax_queue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : (relax A i u S e).queue = S.queue := by
  unfold relax
  dsimp only
  split_ifs <;> rfl

theorem relax_nextRank {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : (relax A i u S e).nextRank = S.nextRank := by
  unfold relax
  dsimp only
  split_ifs <;> rfl

theorem relaxAll_table {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) : (relaxAll A i u S).table = S.table := by
  apply fold_preserves (relax A i u) (fun U => U.table = S.table) _ S rfl
  intro e he U hU
  exact (relax_table A i u U e).trans hU

theorem relaxAll_queue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) : (relaxAll A i u S).queue = S.queue := by
  apply fold_preserves (relax A i u) (fun U => U.queue = S.queue) _ S rfl
  intro e he U hU
  exact (relax_queue A i u U e).trans hU

theorem relaxAll_nextRank {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) : (relaxAll A i u S).nextRank = S.nextRank := by
  apply fold_preserves (relax A i u) (fun U => U.nextRank = S.nextRank) _ S rfl
  intro e he U hU
  exact (relax_nextRank A i u U e).trans hU

theorem picked_mem {k : ℕ} (A : ClockCall k) (S : MultiLayer A.d) (h : S.queue ≠ []) :
    picked A S ∈ S.queue := selectMin_mem _ _ _ h

theorem pop_of_nonempty {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (h : S.queue ≠ []) :
    pop A i S = relaxAll A i (picked A S) (settle S (picked A S) i) := by
  unfold pop
  cases he : S.queue with
  | nil => exact (h he).elim
  | cons v vs => simp [relaxAll, settle, picked, selectMin, he]

theorem pop_queue_length {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : (pop A i S).queue.length = S.queue.length - 1 := by
  by_cases h : S.queue = []
  · simp [pop, h]
  · rw [pop_of_nonempty A i S h, relaxAll_queue]
    exact List.length_erase_of_mem (picked_mem A S h)

theorem pop_queue_sublist {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : (pop A i S).queue.Sublist S.queue := by
  by_cases h : S.queue = []
  · simp [pop, h]
  · rw [pop_of_nonempty A i S h, relaxAll_queue]
    exact List.erase_sublist

theorem runQueue_queue_length {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : (runQueue A i n S).queue.length = S.queue.length - n := by
  induction n with
  | zero => simp [runQueue]
  | succ n ih => rw [runQueue_succ, pop_queue_length, ih]; omega

theorem runQueue_queue_sublist {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : (runQueue A i n S).queue.Sublist S.queue := by
  induction n with
  | zero => exact List.Sublist.refl _
  | succ n ih => rw [runQueue_succ]; exact (pop_queue_sublist A i _).trans ih

theorem constructLayer_queue_empty {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) :
    (runQueue A i (incidentVertices A.I).length (initializeLayer A T i)).queue = [] := by
  apply List.length_eq_zero_iff.mp
  rw [runQueue_queue_length]
  simp [initializeLayer]

theorem put_range {d : ℕ} (T : MultiTable d) (v : ℕ) (i : Fin d → ℕ) (c : MultiCell)
    (hT : MultiRange T) (hc : 0 ≤ c.value ∧ c.value ≤ 1) : MultiRange (put T v i c) := by
  intro w j
  unfold put
  split_ifs
  · exact hc
  · exact hT w j

theorem initializeLayer_range {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hT : MultiRange T) : LayerRange (initializeLayer A T i) := by
  refine ⟨hT, ?_⟩
  intro v
  change 0 ≤ (if v = A.I.source then 0 else _) ∧ (if v = A.I.source then 0 else _) ≤ 1
  split_ifs
  · norm_num
  · cases h : nextTick A T v i
    · norm_num
    · exact value_range A T hT _ _

theorem settle_range {d : ℕ} (S : MultiLayer d) (u : ℕ) (i : Fin d → ℕ)
    (hS : LayerRange S) : LayerRange (settle S u i) :=
  ⟨put_range S.table u i _ hS.1 (hS.2 u), hS.2⟩

theorem relax_range {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (i : Fin A.d → ℕ) (u : ℕ) (S : MultiLayer A.d) (e : ℕ × ℕ)
    (hS : LayerRange S) : LayerRange (relax A i u S e) := by
  unfold relax
  dsimp only
  split_ifs with he hb
  · refine ⟨hS.1, ?_⟩
    intro v
    by_cases hv : v = e.2
    · subst v
      simpa using expectation_range A hδ hL S.table hS.1 u e.2 i
    · simpa [Function.update_of_ne hv] using hS.2 v
  · exact hS
  · exact hS

theorem relaxAll_range {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (i : Fin A.d → ℕ) (u : ℕ) (S : MultiLayer A.d) (hS : LayerRange S) :
    LayerRange (relaxAll A i u S) := by
  apply fold_preserves (relax A i u) LayerRange _ S hS
  intro e he U hU
  exact relax_range A hδ hL i u U e hU

theorem pop_range {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) (hS : LayerRange S) : LayerRange (pop A i S) := by
  by_cases h : S.queue = []
  · simpa [pop, h] using hS
  · rw [pop_of_nonempty A i S h]
    exact relaxAll_range A hδ hL i _ _ (settle_range S _ i hS)

theorem runQueue_range {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (i : Fin A.d → ℕ) (n : ℕ) (S : MultiLayer A.d) (hS : LayerRange S) :
    LayerRange (runQueue A i n S) := by
  induction n with
  | zero => exact hS
  | succ n ih => rw [runQueue_succ]; exact pop_range A hδ hL i _ ih

theorem constructLayer_range {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (T : MultiTable A.d) (i : Fin A.d → ℕ) (hT : MultiRange T) :
    MultiRange (constructLayer A T i) :=
  (runQueue_range A hδ hL i _ _ (initializeLayer_range A T i hT)).1

theorem constructTable_range {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L) :
    MultiRange (constructTable A) := by
  apply fold_preserves (constructLayer A) MultiRange _ _
    (by intro v i; exact ⟨zero_le_one, le_rfl⟩)
  intro i hi T hT
  exact constructLayer_range A hδ hL T i hT

theorem pop_other_index {k : ℕ} (A : ClockCall k) (i j : Fin A.d → ℕ)
    (S : MultiLayer A.d) (v : ℕ) (hij : j ≠ i) :
    (pop A i S).table v j = S.table v j := by
  by_cases h : S.queue = []
  · simp [pop, h]
  · rw [pop_of_nonempty A i S h, relaxAll_table]
    exact put_other _ _ _ _ _ _ (Or.inr hij)

theorem runQueue_other_index {k : ℕ} (A : ClockCall k) (i j : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) (v : ℕ) (hij : j ≠ i) :
    (runQueue A i n S).table v j = S.table v j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runQueue_succ]; exact (pop_other_index A i j _ v hij).trans ih

theorem constructLayer_other_index {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i j : Fin A.d → ℕ) (v : ℕ) (hij : j ≠ i) :
    constructLayer A T i v j = T v j :=
  runQueue_other_index A i j _ _ v hij

theorem relax_keys_le {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) (v : ℕ) :
    (relax A i u S e).keys v ≤ S.keys v := by
  unfold relax
  dsimp only
  split_ifs with he hb
  · by_cases hv : v = e.2
    · subst v
      simpa using hb.le
    · simp [Function.update_of_ne hv]
  · rfl
  · rfl

theorem relaxAll_keys_le {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (v : ℕ) : (relaxAll A i u S).keys v ≤ S.keys v := by
  apply fold_preserves (relax A i u) (fun U => U.keys v ≤ S.keys v) _ S le_rfl
  intro e he U hU
  exact (relax_keys_le A i u U e v).trans hU

theorem pop_keys_le {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (v : ℕ) : (pop A i S).keys v ≤ S.keys v := by
  by_cases h : S.queue = []
  · simp [pop, h]
  · rw [pop_of_nonempty A i S h]
    exact relaxAll_keys_le A i _ _ v

theorem runQueue_keys_le {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) (v : ℕ) : (runQueue A i n S).keys v ≤ S.keys v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runQueue_succ]; exact (pop_keys_le A i _ v).trans ih

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

namespace NearLinearRSP.TwoResources.Supplement

def LayerSync {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (S : MultiLayer A.d) : Prop :=
  ∀ v ∈ incidentVertices A.I, v ∉ S.queue → (S.table v i).value = S.keys v

theorem relax_keys_outside {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) (v : ℕ) (hv : v ∉ S.queue) :
    (relax A i u S e).keys v = S.keys v := by
  unfold relax
  dsimp only
  split_ifs with he hb
  · have hne : v ≠ e.2 := by intro h; exact hv (h.symm ▸ he.2)
    simp [Function.update_of_ne hne]
  · rfl
  · rfl

theorem relax_sync {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) (hS : LayerSync A i S) :
    LayerSync A i (relax A i u S e) := by
  intro v hv hn
  rw [relax_queue] at hn
  rw [relax_table, relax_keys_outside A i u S e v hn]
  exact hS v hv hn

theorem relaxAll_sync {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (hS : LayerSync A i S) : LayerSync A i (relaxAll A i u S) := by
  apply fold_preserves (relax A i u) (LayerSync A i) _ S hS
  intro e he U hU
  exact relax_sync A i u U e hU

theorem settle_sync {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (hS : LayerSync A i S) : LayerSync A i (settle S u i) := by
  intro v hv hn
  by_cases he : v = u
  · subst v
    simp [settle, put_same]
  · have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne he).mpr hm)
    change (put S.table u i _ v i).value = S.keys v
    rw [put_other _ _ _ _ _ _ (Or.inl he)]
    exact hS v hv hn'

theorem initializeLayer_sync {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (T : MultiTable A.d) : LayerSync A i (initializeLayer A T i) := by
  intro v hv hn
  exact (hn hv).elim

theorem pop_sync {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerSync A i S) : LayerSync A i (pop A i S) := by
  by_cases h : S.queue = []
  · simpa [pop, h] using hS
  · rw [pop_of_nonempty A i S h]
    exact relaxAll_sync A i _ _ (settle_sync A i _ S hS)

theorem runQueue_sync {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) (hS : LayerSync A i S) :
    LayerSync A i (runQueue A i n S) := by
  induction n with
  | zero => exact hS
  | succ n ih => rw [runQueue_succ]; exact pop_sync A i _ ih

theorem constructLayer_le_initial {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (v : ℕ) (hv : v ∈ incidentVertices A.I) :
    (constructLayer A T i v i).value ≤ (initializeLayer A T i).keys v := by
  have hs := runQueue_sync A i (incidentVertices A.I).length _ (initializeLayer_sync A i T)
  have he := constructLayer_queue_empty A T i
  have hvalue := hs v hv (by rw [he]; simp)
  change ((runQueue A i (incidentVertices A.I).length (initializeLayer A T i)).table v i).value ≤ _
  rw [hvalue]
  exact runQueue_keys_le A i _ _ v

theorem constructLayer_source {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d) (hT : MultiRange T)
    (i : Fin A.d → ℕ) : (constructLayer A T i A.I.source i).value = 0 := by
  have hl := constructLayer_le_initial A T i A.I.source (incident_source_mem A.I)
  have h0 := (constructLayer_range A hδ hL T i hT A.I.source i).1
  simp only [initializeLayer, if_pos rfl] at hl
  exact le_antisymm hl h0

theorem initializeLayer_le_tick {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (hT : MultiRange T) (i : Fin A.d → ℕ) (v : ℕ) (j : Fin A.d) :
    (initializeLayer A T i).keys v ≤ value A T v (Function.update i j (i j + 1)) := by
  by_cases hv : v = A.I.source
  · simpa only [initializeLayer, if_pos hv] using (value_range A T hT v _).1
  · simp only [initializeLayer, if_neg hv, nextTick]
    cases hr : List.finRange A.d with
    | nil =>
      have hm : j ∈ List.finRange A.d := by simp
      rw [hr] at hm
      cases hm
    | cons r rs =>
      exact selectMin_le_mem
        (fun s : Fin A.d => value A T v (Function.update i s (i s + 1)))
        (r :: rs) r j (by rw [← hr]; simp)

theorem constructLayer_le_tick {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (hT : MultiRange T) (i : Fin A.d → ℕ) (v : ℕ) (hv : v ∈ incidentVertices A.I)
    (j : Fin A.d) :
    (constructLayer A T i v i).value ≤ value A T v (Function.update i j (i j + 1)) :=
  (constructLayer_le_initial A T i v hv).trans (initializeLayer_le_tick A T hT i v j)

theorem vectors_ordered (d q : ℕ) :
    (vectors d q).Pairwise (fun i j => vectorIndex q i < vectorIndex q j) := by
  induction d with
  | zero => simp [vectors]
  | succ d ih =>
    rw [vectors, List.pairwise_flatMap]
    constructor
    · intro a ha
      apply List.pairwise_map.mpr
      exact ih.imp (fun {_ _} h => by simpa only [vectorIndex_cons] using Nat.add_lt_add_left h (a * q ^ d))
    · apply (List.pairwise_lt_range : (List.range q).Pairwise (· < ·)).imp
      intro a b hab i hi j hj
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hj
      rw [vectorIndex_cons, vectorIndex_cons]
      have hx' := vectorIndex_lt x ((mem_vectors x).mp hx)
      have hh := Nat.mul_le_mul_right (q ^ d) (Nat.succ_le_of_lt hab)
      nlinarith

noncomputable def runLayers {k : ℕ} (A : ClockCall k) (xs : List (Fin A.d → ℕ))
    (T : MultiTable A.d) : MultiTable A.d := xs.foldl (constructLayer A) T

theorem runLayers_range {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (xs : List (Fin A.d → ℕ)) (T : MultiTable A.d) (hT : MultiRange T) :
    MultiRange (runLayers A xs T) := by
  apply fold_preserves (constructLayer A) MultiRange xs T hT
  intro i hi U hU
  exact constructLayer_range A hδ hL U i hU

theorem runLayers_frame {k : ℕ} (A : ClockCall k) (xs : List (Fin A.d → ℕ))
    (T : MultiTable A.d) (v : ℕ) (j : Fin A.d → ℕ) (hj : j ∉ xs) :
    runLayers A xs T v j = T v j := by
  induction xs generalizing T with
  | nil => rfl
  | cons i xs ih =>
    have hn : j ≠ i := fun h => hj (by simp [h])
    have ht : j ∉ xs := fun hm => hj (by simp [hm])
    change runLayers A xs (constructLayer A T i) v j = T v j
    rw [ih _ ht, constructLayer_other_index A T i j v hn]

theorem constructTable_layer_witness {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) :
    ∃ T : MultiTable A.d, MultiRange T ∧
      ∀ v j, vectorIndex A.q i ≤ vectorIndex A.q j →
        constructTable A v j = constructLayer A T i v j := by
  have hm : i ∈ (vectors A.d A.q).reverse := by
    simpa only [List.mem_reverse] using (mem_vectors i).mpr hi
  obtain ⟨pre, post, hs⟩ := List.mem_iff_append.mp hm
  let T : MultiTable A.d := runLayers A pre (fun _ _ => ⟨1, .none, 0⟩)
  refine ⟨T, runLayers_range A hδ hL pre _ (by intro v j; exact ⟨zero_le_one, le_rfl⟩), ?_⟩
  intro v j hj
  have hord : ((vectors A.d A.q).reverse).Pairwise
      (fun a b => vectorIndex A.q b < vectorIndex A.q a) :=
    List.pairwise_reverse.mpr (vectors_ordered A.d A.q)
  rw [hs] at hord
  have hpost : ∀ p ∈ post, vectorIndex A.q p < vectorIndex A.q i :=
    (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1
  have hj' : j ∉ post := by intro hm; have hh := hpost j hm; omega
  unfold constructTable
  rw [hs, List.foldl_append, List.foldl_cons]
  exact runLayers_frame A post (constructLayer A T i) v j hj'

theorem constructTable_source {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) :
    (constructTable A A.I.source i).value = 0 := by
  obtain ⟨T, hT, he⟩ := constructTable_layer_witness A hδ hL i hi
  rw [he A.I.source i le_rfl]
  exact constructLayer_source A hδ hL T hT i

theorem constructTable_tick_monotone {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (v : ℕ) (hv : v ∈ incidentVertices A.I)
    (i : Fin A.d → ℕ) (j : Fin A.d) :
    value A (constructTable A) v i ≤
      value A (constructTable A) v (Function.update i j (i j + 1)) := by
  classical
  let i' := Function.update i j (i j + 1)
  have hle : ∀ r, i r ≤ i' r := by
    intro r
    by_cases hr : r = j
    · subst r
      simp [i']
    · simp [i', Function.update_of_ne hr]
  have hne : i' ≠ i := by
    intro he
    have hh := congrFun he j
    simp [i'] at hh
  by_cases hi : ∀ r, i r < A.q
  · by_cases hi' : ∀ r, i' r < A.q
    · have hq : 0 < A.q := (Nat.zero_le (i j)).trans_lt (hi j)
      have hidx := (vectorIndex_lt_of_le hq i i' hle (Ne.symm hne)).le
      obtain ⟨T, hT, he⟩ := constructTable_layer_witness A hδ hL i hi
      have hf : constructTable A v i' = T v i' :=
        (he v i' hidx).trans (constructLayer_other_index A T i i' v hne)
      have hb := constructLayer_le_tick A T hT i v hv j
      rw [value_of_valid A T v i' hi'] at hb
      rw [value_of_valid A (constructTable A) v i hi, he v i le_rfl]
      change (constructLayer A T i v i).value ≤ value A (constructTable A) v i'
      rw [value_of_valid A (constructTable A) v i' hi', hf]
      exact hb
    · have hs : ∃ r, A.q ≤ i' r := by simpa using hi'
      change value A (constructTable A) v i ≤ value A (constructTable A) v i'
      rw [value_of_saturated A (constructTable A) v i' hs]
      exact (value_range A (constructTable A) (constructTable_range A hδ hL) v i).2
  · have hs : ∃ r, A.q ≤ i r := by simpa using hi
    have hs' : ∃ r, A.q ≤ i' r := by
      obtain ⟨r, hr⟩ := hs
      exact ⟨r, hr.trans (hle r)⟩
    change value A (constructTable A) v i ≤ value A (constructTable A) v i'
    rw [value_of_saturated A (constructTable A) v i hs,
      value_of_saturated A (constructTable A) v i' hs']

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace NearLinearRSP.TwoResources.Supplement

theorem monotone_of_coordinate_steps {d : ℕ} (f : (Fin d → ℕ) → ℝ)
    (hstep : ∀ i r, f i ≤ f (Function.update i r (i r + 1)))
    (i j : Fin d → ℕ) (hij : ∀ r, i r ≤ j r) : f i ≤ f j := by
  classical
  have hmany (x : Fin d → ℕ) (r : Fin d) (n : ℕ) :
      f x ≤ f (Function.update x r (x r + n)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep (Function.update x r (x r + n)) r
      simpa [Function.update_idem, Nat.add_assoc] using ih.trans hs
  have hfinite (s : Finset (Fin d)) :
      f i ≤ f (fun r => if r ∈ s then j r else i r) := by
    induction s using Finset.induction_on with
    | empty => simpa using (le_refl (f i))
    | @insert r s hrs ih =>
      let x : Fin d → ℕ := fun a => if a ∈ s then j a else i a
      have hx : x r = i r := by simp [x, hrs]
      have hu : Function.update x r (x r + (j r - i r)) =
          (fun a => if a ∈ insert r s then j a else i a) := by
        funext a
        by_cases ha : a = r
        · subst a
          simp [hx, Nat.add_sub_of_le (hij r)]
        · simp [Function.update_of_ne ha, x, ha]
      exact ih.trans (hu ▸ hmany x r (j r - i r))
  simpa using hfinite Finset.univ

theorem constructTable_monotone {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (v : ℕ)
    (hv : v ∈ incidentVertices A.I) (i j : Fin A.d → ℕ)
    (hij : ∀ r, i r ≤ j r) :
    value A (constructTable A) v i ≤ value A (constructTable A) v j := by
  exact monotone_of_coordinate_steps (value A (constructTable A) v)
    (constructTable_tick_monotone A hδ hL v hv) i j hij

theorem expectation_lower_bound {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (u v : ℕ) (i : Fin A.d → ℕ) (b : ℝ) (hb : b ≤ 1)
    (hvalues : ∀ a ∈ rectangle A i, b ≤ value A T u (fun r => i r + a r)) :
    b ≤ expectation A T u v i := by
  let mass := ((rectangle A i).map (incrementMass A u v)).sum
  have hm : mass ≤ 1 := rectangle_mass_le_one A hδ hL u v i
  have hs : mass * b ≤
      ((rectangle A i).map
        (fun a => incrementMass A u v a * value A T u (fun r => i r + a r))).sum := by
    rw [show mass * b = ((rectangle A i).map (fun a => incrementMass A u v a * b)).sum
      from (List.sum_map_mul_right _ _ _).symm]
    apply List.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (hvalues a ha) (incrementMass_nonneg A hδ hL u v a)
  unfold expectation
  change b ≤ 1 - mass + _
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hb)]

theorem expectation_congr {k : ℕ} (A : ClockCall k) (T U : MultiTable A.d)
    (u v : ℕ) (i : Fin A.d → ℕ)
    (h : ∀ a ∈ rectangle A i,
      value A T u (fun r => i r + a r) = value A U u (fun r => i r + a r)) :
    expectation A T u v i = expectation A U u v i := by
  unfold expectation
  dsimp only
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [h a ha]

theorem value_congr_vertex {k : ℕ} (A : ClockCall k) (T U : MultiTable A.d)
    (u : ℕ) (i : Fin A.d → ℕ) (h : T u i = U u i) :
    value A T u i = value A U u i := by
  unfold value
  rw [h]

def FutureLower {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) : Prop :=
  ∀ v ∈ incidentVertices A.I, ∀ a ∈ rectangle A i, a ≠ (fun _ => 0) →
    (initializeLayer A T i).keys v ≤ value A T v (fun r => i r + a r)

theorem layer_futureLower_from_final {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d) (hT : MultiRange T)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q)
    (he : ∀ v j, vectorIndex A.q i < vectorIndex A.q j →
      T v j = constructTable A v j) : FutureLower A T i := by
  classical
  intro v hv a ha ha0
  have hex : ∃ r, a r ≠ 0 := by
    by_contra hn
    apply ha0
    funext r
    simpa using (not_exists.mp hn r)
  obtain ⟨r, hr⟩ := hex
  let j := Function.update i r (i r + 1)
  let b := fun s => i s + a s
  have hab : ∀ s, b s < A.q := (rectangle_mem A i a).mp ha
  have hij : ∀ s, i s ≤ j s := by
    intro s
    by_cases hs : s = r
    · subst s; simp [j]
    · simp [j, Function.update_of_ne hs]
  have hjb : ∀ s, j s ≤ b s := by
    intro s
    by_cases hs : s = r
    · subst s; simp [j, b]; omega
    · simp [j, b, Function.update_of_ne hs]
  have hj : ∀ s, j s < A.q := fun s => (hjb s).trans_lt (hab s)
  have hijne : i ≠ j := by
    intro h
    have hh := congrFun h r
    simp [j] at hh
  have hibne : i ≠ b := by
    intro h
    have hh := congrFun h r
    dsimp [b] at hh
    omega
  have hq : 0 < A.q := (Nat.zero_le (i r)).trans_lt (hi r)
  have hej := he v j (vectorIndex_lt_of_le hq i j hij hijne)
  have heb := he v b (vectorIndex_lt_of_le hq i b (fun s => Nat.le_add_right _ _) hibne)
  have htick := initializeLayer_le_tick A T hT i v r
  change (initializeLayer A T i).keys v ≤ value A T v b
  have hmon := constructTable_monotone A hδ hL v hv j b hjb
  rw [value_of_valid A T v j hj, hej] at htick
  rw [value_of_valid A (constructTable A) v j hj,
    value_of_valid A (constructTable A) v b hab] at hmon
  rw [value_of_valid A T v b hab, heb]
  exact htick.trans hmon

theorem constructTable_layer_witness_strong {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) :
    ∃ T : MultiTable A.d, MultiRange T ∧ FutureLower A T i ∧
      ∀ v j, vectorIndex A.q i ≤ vectorIndex A.q j →
        constructTable A v j = constructLayer A T i v j := by
  obtain ⟨T, hT, he⟩ := constructTable_layer_witness A hδ hL i hi
  refine ⟨T, hT, layer_futureLower_from_final A hδ hL T hT i hi ?_, he⟩
  intro v j hj
  have hne : j ≠ i := by intro h; subst j; exact (lt_irrefl _ hj)
  exact ((he v j hj.le).trans (constructLayer_other_index A T i j v hne)).symm

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

def LayerOrder {k : ℕ} (A : ClockCall k) (S : MultiLayer A.d) : Prop :=
  ∀ u ∈ incidentVertices A.I, u ∉ S.queue → ∀ v ∈ S.queue, S.keys u ≤ S.keys v

structure LayerInvariant {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) : Prop where
  range : LayerRange S
  sync : LayerSync A i S
  nodup : S.queue.Nodup
  subset : ∀ v ∈ S.queue, v ∈ incidentVertices A.I
  frame : ∀ v j, j ≠ i → S.table v j = T v j
  initial : ∀ v, S.keys v ≤ (initializeLayer A T i).keys v
  order : LayerOrder A S

theorem incident_nodup {k : ℕ} (I : MultiInstance k) : (incidentVertices I).Nodup := by
  exact activeVertices_nodup (lengthInstance I)

theorem initializeLayer_invariant {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hT : MultiRange T) :
    LayerInvariant A T i (initializeLayer A T i) := by
  refine ⟨initializeLayer_range A T i hT, initializeLayer_sync A i T,
    incident_nodup A.I, ?_, ?_, ?_, ?_⟩
  · intro v hv; exact hv
  · intro v j hj; rfl
  · intro v; rfl
  · intro u hu hn; exact (hn hu).elim

theorem picked_le {k : ℕ} (A : ClockCall k) (S : MultiLayer A.d)
    (v : ℕ) (hv : v ∈ S.queue) : S.keys (picked A S) ≤ S.keys v :=
  selectMin_le_mem S.keys S.queue A.I.source v hv

theorem settle_invariant {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) (hS : LayerInvariant A T i S)
    (hn : S.queue ≠ []) : LayerInvariant A T i (settle S (picked A S) i) := by
  let u := picked A S
  have hu : u ∈ S.queue := picked_mem A S hn
  refine ⟨settle_range S u i hS.range, settle_sync A i u S hS.sync,
    hS.nodup.erase u, ?_, ?_, hS.initial, ?_⟩
  · intro v hv
    exact hS.subset v (List.mem_of_mem_erase hv)
  · intro v j hj
    exact (put_other S.table u v i j _ (Or.inr hj)).trans (hS.frame v j hj)
  · intro w hw hwn v hv
    have hv' : v ∈ S.queue := List.mem_of_mem_erase hv
    by_cases hwu : w = u
    · subst w
      exact picked_le A S v hv'
    · have hw' : w ∉ S.queue := fun hm => hwn ((List.mem_erase_of_ne hwu).mpr hm)
      exact hS.order w hw hw' v hv'

theorem settle_picked_upper {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) (hS : LayerInvariant A T i S)
    (hn : S.queue ≠ []) (v : ℕ) (hv : v ∈ incidentVertices A.I)
    (hvn : v ∉ (settle S (picked A S) i).queue) :
    (settle S (picked A S) i).keys v ≤ (settle S (picked A S) i).keys (picked A S) := by
  by_cases h : v = picked A S
  · subst v; rfl
  · have hv' : v ∉ S.queue := fun hm => hvn ((List.mem_erase_of_ne h).mpr hm)
    exact hS.order v hv hv' _ (picked_mem A S hn)

theorem expectation_ge_settled_key {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hf : FutureLower A T i)
    (S : MultiLayer A.d) (hS : LayerInvariant A T i S)
    (u v : ℕ) (hu : u ∈ incidentVertices A.I) (hun : u ∉ S.queue) :
    S.keys u ≤ expectation A S.table u v i := by
  apply expectation_lower_bound A hδ hL S.table u v i (S.keys u) (hS.range.2 u).2
  intro a ha
  by_cases ha0 : a = (fun _ => 0)
  · subst a
    simp only [Nat.add_zero]
    rw [value_of_valid A S.table u i hi, hS.sync u hu hun]
  · have hne : (fun r => i r + a r) ≠ i := by
      intro he
      apply ha0
      funext r
      have hh := congrFun he r
      omega
    rw [value_congr_vertex A S.table T u _ (hS.frame u _ hne)]
    exact (hS.initial u).trans (hf u hu a ha ha0)

theorem relax_invariant {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hf : FutureLower A T i)
    (S : MultiLayer A.d) (hS : LayerInvariant A T i S)
    (u : ℕ) (hu : u ∈ incidentVertices A.I) (hun : u ∉ S.queue)
    (hupper : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → S.keys v ≤ S.keys u)
    (e : ℕ × ℕ) : LayerInvariant A T i (relax A i u S e) := by
  refine ⟨relax_range A hδ hL i u S e hS.range, relax_sync A i u S e hS.sync,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [relax_queue]; exact hS.nodup
  · intro v hv
    rw [relax_queue] at hv
    exact hS.subset v hv
  · intro v j hj
    rw [relax_table]; exact hS.frame v j hj
  · intro v
    exact (relax_keys_le A i u S e v).trans (hS.initial v)
  · intro w hw hwn v hv
    rw [relax_queue] at hwn hv
    rw [relax_keys_outside A i u S e w hwn]
    have hbound := expectation_ge_settled_key A hδ hL T i hi hf S hS u e.2 hu hun
    unfold relax
    dsimp only
    split_ifs with he hb
    · by_cases heq : v = e.2
      · subst v
        simpa using (hupper w hw hwn).trans hbound
      · simpa [Function.update_of_ne heq] using hS.order w hw hwn v hv
    · exact hS.order w hw hwn v hv
    · exact hS.order w hw hwn v hv

theorem relax_upper {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (u : ℕ) (hun : u ∉ S.queue)
    (hupper : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → S.keys v ≤ S.keys u)
    (e : ℕ × ℕ) :
    ∀ v ∈ incidentVertices A.I, v ∉ (relax A i u S e).queue →
      (relax A i u S e).keys v ≤ (relax A i u S e).keys u := by
  intro v hv hn
  rw [relax_queue] at hn
  rw [relax_keys_outside A i u S e v hn, relax_keys_outside A i u S e u hun]
  exact hupper v hv hn

theorem relaxAll_invariant {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hf : FutureLower A T i)
    (S : MultiLayer A.d) (hS : LayerInvariant A T i S)
    (u : ℕ) (hu : u ∈ incidentVertices A.I) (hun : u ∉ S.queue)
    (hupper : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → S.keys v ≤ S.keys u) :
    LayerInvariant A T i (relaxAll A i u S) := by
  have h : ∀ U, U = relaxAll A i u S →
      LayerInvariant A T i U ∧ u ∉ U.queue ∧
        (∀ v ∈ incidentVertices A.I, v ∉ U.queue → U.keys v ≤ U.keys u) := by
    intro U hU
    subst U
    apply fold_preserves (relax A i u)
      (fun U => LayerInvariant A T i U ∧ u ∉ U.queue ∧
        (∀ v ∈ incidentVertices A.I, v ∉ U.queue → U.keys v ≤ U.keys u))
      _ S ⟨hS, hun, hupper⟩
    intro e he U hU
    refine ⟨relax_invariant A hδ hL T i hi hf U hU.1 u hu hU.2.1 hU.2.2 e,
      ?_, relax_upper A i U u hU.2.1 hU.2.2 e⟩
    rw [relax_queue]; exact hU.2.1
  exact (h _ rfl).1

theorem pop_invariant {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hf : FutureLower A T i)
    (S : MultiLayer A.d) (hS : LayerInvariant A T i S) :
    LayerInvariant A T i (pop A i S) := by
  by_cases hn : S.queue = []
  · simpa [pop, hn] using hS
  · rw [pop_of_nonempty A i S hn]
    apply relaxAll_invariant A hδ hL T i hi hf _ (settle_invariant A T i S hS hn)
      _ (hS.subset _ (picked_mem A S hn))
    · exact hS.nodup.not_mem_erase
    · exact settle_picked_upper A T i S hS hn

theorem runQueue_invariant {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hf : FutureLower A T i)
    (n : ℕ) (S : MultiLayer A.d) (hS : LayerInvariant A T i S) :
    LayerInvariant A T i (runQueue A i n S) := by
  induction n with
  | zero => exact hS
  | succ n ih => rw [runQueue_succ]; exact pop_invariant A hδ hL T i hi hf _ ih

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem relaxFold_keys_le {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (es : List (ℕ × ℕ)) (S : MultiLayer A.d) (v : ℕ) :
    (es.foldl (relax A i u) S).keys v ≤ S.keys v := by
  apply fold_preserves (relax A i u) (fun U => U.keys v ≤ S.keys v) es S le_rfl
  intro e he U hU
  exact (relax_keys_le A i u U e v).trans hU

theorem relax_le_edge {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (u v : ℕ) (S : MultiLayer A.d) (hv : v ∈ S.queue) :
    (relax A i u S (u, v)).keys v ≤ expectation A S.table u v i := by
  unfold relax
  dsimp only
  rw [if_pos ⟨rfl, hv⟩]
  split_ifs with h
  · simp
  · exact le_of_not_gt h

theorem relaxFold_le_edge {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (u v : ℕ) (es : List (ℕ × ℕ)) (S : MultiLayer A.d)
    (hv : v ∈ S.queue) (he : (u, v) ∈ es) :
    (es.foldl (relax A i u) S).keys v ≤ expectation A S.table u v i := by
  induction es generalizing S with
  | nil => simp at he
  | cons e es ih =>
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact (relaxFold_keys_le A i u es _ v).trans (relax_le_edge A i u v S hv)
    · have hv' : v ∈ (relax A i u S e).queue := by rw [relax_queue]; exact hv
      have hh := ih (relax A i u S e) hv' he
      rw [relax_table] at hh
      exact hh

theorem expectation_settle_other {k : ℕ} (A : ClockCall k)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) (u w v : ℕ) (hwu : w ≠ u) :
    expectation A (settle S u i).table w v i = expectation A S.table w v i := by
  apply expectation_congr
  intro a ha
  exact value_congr_vertex A _ _ w _ (put_other _ _ _ _ _ _ (Or.inl hwu))

def LayerBellman {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : Prop :=
  ∀ u ∈ incidentVertices A.I, u ∉ S.queue →
    ∀ v ∈ incidentVertices A.I, (u, v) ∈ callEdges A →
      S.keys v ≤ expectation A S.table u v i

theorem initializeLayer_bellman {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) : LayerBellman A i (initializeLayer A T i) := by
  intro u hu hn
  exact (hn hu).elim

theorem pop_bellman {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hf : FutureLower A T i)
    (S : MultiLayer A.d) (hS : LayerInvariant A T i S) (hb : LayerBellman A i S) :
    LayerBellman A i (pop A i S) := by
  by_cases hn : S.queue = []
  · simpa [pop, hn] using hb
  · rw [pop_of_nonempty A i S hn]
    let u := picked A S
    let U := settle S u i
    have hU : LayerInvariant A T i U := settle_invariant A T i S hS hn
    have hu : u ∈ incidentVertices A.I := hS.subset u (picked_mem A S hn)
    have hun : u ∉ U.queue := hS.nodup.not_mem_erase
    intro w hw hwn v hv he
    rw [relaxAll_queue] at hwn
    rw [relaxAll_table]
    by_cases hwu : w = u
    · subst w
      by_cases hvn : v ∈ U.queue
      · exact relaxFold_le_edge A i u v (callEdges A) U hvn he
      · have hupper : U.keys v ≤ U.keys u := settle_picked_upper A T i S hS hn v hv hvn
        exact (relaxAll_keys_le A i u U v).trans
          (hupper.trans (expectation_ge_settled_key A hδ hL T i hi hf U hU u v hu hun))
    · have hwn' : w ∉ S.queue := fun hm => hwn ((List.mem_erase_of_ne hwu).mpr hm)
      rw [expectation_settle_other A i S u w v hwu]
      exact (relaxAll_keys_le A i u U v).trans (hb w hw hwn' v hv he)

theorem runQueue_bellman {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hf : FutureLower A T i)
    (n : ℕ) (S : MultiLayer A.d) (hS : LayerInvariant A T i S) (hb : LayerBellman A i S) :
    LayerBellman A i (runQueue A i n S) := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    rw [runQueue_succ]
    exact pop_bellman A hδ hL T i hi hf _
      (runQueue_invariant A hδ hL T i hi hf n S hS) ih

theorem constructLayer_bellman {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d) (hT : MultiRange T)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hf : FutureLower A T i)
    (u v : ℕ) (hu : u ∈ incidentVertices A.I) (hv : v ∈ incidentVertices A.I)
    (he : (u, v) ∈ callEdges A) :
    (constructLayer A T i v i).value ≤ expectation A (constructLayer A T i) u v i := by
  let S := runQueue A i (incidentVertices A.I).length (initializeLayer A T i)
  have hS : LayerInvariant A T i S := runQueue_invariant A hδ hL T i hi hf _ _ (initializeLayer_invariant A T i hT)
  have hb : LayerBellman A i S := runQueue_bellman A hδ hL T i hi hf _ _
    (initializeLayer_invariant A T i hT) (initializeLayer_bellman A T i)
  have hq : S.queue = [] := constructLayer_queue_empty A T i
  have hu' : u ∉ S.queue := by rw [hq]; simp
  have hv' : v ∉ S.queue := by rw [hq]; simp
  change (S.table v i).value ≤ expectation A S.table u v i
  rw [hS.sync v hv hv']
  exact hb u hu hu' v hv he

theorem constructTable_bellman {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (i : Fin A.d → ℕ)
    (u v : ℕ) (hu : u ∈ incidentVertices A.I) (hv : v ∈ incidentVertices A.I)
    (he : (u, v) ∈ callEdges A) :
    value A (constructTable A) v i ≤ expectation A (constructTable A) u v i := by
  classical
  by_cases hi : ∀ r, i r < A.q
  · obtain ⟨T, hT, hf, ht⟩ := constructTable_layer_witness_strong A hδ hL i hi
    have hcon : expectation A (constructTable A) u v i =
        expectation A (constructLayer A T i) u v i := by
      apply expectation_congr
      intro a ha
      apply value_congr_vertex
      exact ht u _ (vectorIndex_le _ _ (fun r => Nat.le_add_right _ _))
    rw [value_of_valid A (constructTable A) v i hi, ht v i le_rfl, hcon]
    exact constructLayer_bellman A hδ hL T hT i hi hf u v hu hv he
  · have hs : ∃ r, A.q ≤ i r := by simpa using hi
    have hr : rectangle A i = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      have hvalid := (rectangle_mem A i a).mp ha
      obtain ⟨r, hr⟩ := hs
      have hb := hvalid r
      omega
    simp [value_of_saturated A (constructTable A) v i hs, expectation, hr]

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

def KeyParent {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (v : ℕ) : Prop :=
  match S.parents v with
  | .none => v = A.I.source ∨ S.keys v = 1
  | .tick j => ∃ h : j < A.d,
      S.keys v = value A S.table v (Function.update i ⟨j, h⟩ (i ⟨j, h⟩ + 1))
  | .edge u => (u, v) ∈ callEdges A ∧ u ∈ incidentVertices A.I ∧ u ∉ S.queue ∧
      S.keys v = expectation A S.table u v i

structure LayerParents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : Prop where
  valid : ∀ v ∈ incidentVertices A.I, KeyParent A i S v
  sync : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → (S.table v i).parent = S.parents v
  rank : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → (S.table v i).rank < S.nextRank
  before : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → ∀ u, S.parents v = .edge u →
    (S.table u i).rank < (S.table v i).rank

theorem initializeLayer_parents {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) : LayerParents A i (initializeLayer A T i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    by_cases hs : v = A.I.source
    · simp [KeyParent, initializeLayer, hs]
    · cases ht : nextTick A T v i with
      | none => simp [KeyParent, initializeLayer, hs, ht]
      | some r =>
        simp only [KeyParent, initializeLayer, if_neg hs, ht]
        exact ⟨r.isLt, trivial⟩
  · intro v hv hn; exact (hn hv).elim
  · intro v hv hn; exact (hn hv).elim
  · intro v hv hn; exact (hn hv).elim

theorem tick_index_ne {d : ℕ} (i : Fin d → ℕ) (r : Fin d) :
    Function.update i r (i r + 1) ≠ i := by
  intro h
  have hh := congrFun h r
  simp at hh

theorem settle_keyParent {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (u v : ℕ) (hu : u ∈ S.queue)
    (h : KeyParent A i S v) : KeyParent A i (settle S u i) v := by
  unfold KeyParent at h ⊢
  change (match S.parents v with
    | .none => _
    | .tick j => _
    | .edge w => _)
  cases hp : S.parents v with
  | none => simpa [hp, settle] using h
  | tick j =>
    rw [hp] at h
    obtain ⟨hj, he⟩ := h
    refine ⟨hj, ?_⟩
    change S.keys v = value A (settle S u i).table v _
    have hf : (settle S u i).table v (Function.update i ⟨j, hj⟩ (i ⟨j, hj⟩ + 1)) =
        S.table v (Function.update i ⟨j, hj⟩ (i ⟨j, hj⟩ + 1)) :=
      put_other S.table u v i _ _ (Or.inr (tick_index_ne i ⟨j, hj⟩))
    rw [value_congr_vertex A _ S.table v _ hf]
    exact he
  | edge w =>
    rw [hp] at h
    have hwu : w ≠ u := fun he => h.2.2.1 (he.symm ▸ hu)
    refine ⟨h.1, h.2.1, ?_, ?_⟩
    · exact fun hm => h.2.2.1 (List.mem_of_mem_erase hm)
    · change S.keys v = expectation A (settle S u i).table w v i
      rw [expectation_settle_other A i S u w v hwu]
      exact h.2.2.2

theorem settle_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerParents A i S)
    (u : ℕ) (hu : u ∈ S.queue) (huv : u ∈ incidentVertices A.I) :
    LayerParents A i (settle S u i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    exact settle_keyParent A i S u v hu (hS.valid v hv)
  · intro v hv hn
    by_cases h : v = u
    · subst v; simp [settle, put_same]
    · have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne h).mpr hm)
      change (put S.table u i _ v i).parent = S.parents v
      rw [put_other _ _ _ _ _ _ (Or.inl h)]
      exact hS.sync v hv hn'
  · intro v hv hn
    by_cases h : v = u
    · subst v; simp [settle, put_same]
    · have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne h).mpr hm)
      change (put S.table u i _ v i).rank < S.nextRank + 1
      rw [put_other _ _ _ _ _ _ (Or.inl h)]
      exact (hS.rank v hv hn').trans (Nat.lt_succ_self _)
  · intro v hv hn w hp
    have hp' : S.parents v = .edge w := hp
    have hvalid := hS.valid v hv
    unfold KeyParent at hvalid
    rw [hp'] at hvalid
    have hwu : w ≠ u := fun he => hvalid.2.2.1 (he.symm ▸ hu)
    change (put S.table u i _ w i).rank < (put S.table u i _ v i).rank
    rw [put_other _ _ _ _ _ _ (Or.inl hwu)]
    by_cases h : v = u
    · subst v
      rw [put_same]
      exact hS.rank w hvalid.2.1 hvalid.2.2.1
    · rw [put_other _ _ _ _ _ _ (Or.inl h)]
      have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne h).mpr hm)
      exact hS.before v hv hn' w hp'

theorem relax_parents_outside {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (u : ℕ) (S : MultiLayer A.d) (e : ℕ × ℕ) (v : ℕ) (hv : v ∉ S.queue) :
    (relax A i u S e).parents v = S.parents v := by
  unfold relax
  dsimp only
  split_ifs with he hb
  · have hne : v ≠ e.2 := by intro h; exact hv (h.symm ▸ he.2)
    simp [Function.update_of_ne hne]
  · rfl
  · rfl

theorem relax_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerParents A i S) (u : ℕ)
    (hu : u ∈ incidentVertices A.I) (hun : u ∉ S.queue)
    (e : ℕ × ℕ) (he : e ∈ callEdges A) : LayerParents A i (relax A i u S e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    unfold relax
    dsimp only
    split_ifs with hc hb
    · by_cases hve : v = e.2
      · subst v
        simp only [KeyParent, Function.update_self]
        exact ⟨by simpa only [hc.1] using (show (e.1, e.2) ∈ callEdges A from he), hu, hun, trivial⟩
      · have hvp := hS.valid v hv
        simpa only [KeyParent, Function.update_of_ne hve] using hvp
    · exact hS.valid v hv
    · exact hS.valid v hv
  · intro v hv hn
    rw [relax_queue] at hn
    rw [relax_table, relax_parents_outside A i u S e v hn]
    exact hS.sync v hv hn
  · intro v hv hn
    rw [relax_queue] at hn
    rw [relax_table, relax_nextRank]
    exact hS.rank v hv hn
  · intro v hv hn w hp
    rw [relax_queue] at hn
    rw [relax_parents_outside A i u S e v hn] at hp
    rw [relax_table]
    exact hS.before v hv hn w hp

theorem relaxAll_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerParents A i S) (u : ℕ)
    (hu : u ∈ incidentVertices A.I) (hun : u ∉ S.queue) :
    LayerParents A i (relaxAll A i u S) := by
  have hh : LayerParents A i (relaxAll A i u S) ∧ u ∉ (relaxAll A i u S).queue := by
    apply fold_preserves (relax A i u) (fun U => LayerParents A i U ∧ u ∉ U.queue)
      (callEdges A) S ⟨hS, hun⟩
    intro e he U hU
    refine ⟨relax_parents A i U hU.1 u hu hU.2 e he, ?_⟩
    rw [relax_queue]; exact hU.2
  exact hh.1

theorem pop_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerParents A i S) (hnodup : S.queue.Nodup)
    (hsub : ∀ v ∈ S.queue, v ∈ incidentVertices A.I) : LayerParents A i (pop A i S) := by
  by_cases hn : S.queue = []
  · simpa [pop, hn] using hS
  · rw [pop_of_nonempty A i S hn]
    have hu := picked_mem A S hn
    exact relaxAll_parents A i _ (settle_parents A i S hS _ hu (hsub _ hu))
      _ (hsub _ hu) hnodup.not_mem_erase

theorem runQueue_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) (hS : LayerParents A i S) (hnodup : S.queue.Nodup)
    (hsub : ∀ v ∈ S.queue, v ∈ incidentVertices A.I) :
    LayerParents A i (runQueue A i n S) := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    rw [runQueue_succ]
    have hss := runQueue_queue_sublist A i n S
    exact pop_parents A i _ ih (hnodup.sublist hss) (fun v hv => hsub v (hss.subset hv))

theorem runQueue_rank_le {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : (runQueue A i n S).nextRank ≤ S.nextRank + n := by
  induction n with
  | zero => simp [runQueue_zero]
  | succ n ih =>
    rw [runQueue_succ]
    by_cases hn : (runQueue A i n S).queue = []
    · simp only [pop, hn]
      omega
    · rw [pop_of_nonempty A i _ hn, relaxAll_nextRank]
      change (runQueue A i n S).nextRank + 1 ≤ S.nextRank + (n + 1)
      omega

def TableParents {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) : Prop :=
  ∀ v ∈ incidentVertices A.I,
    (T v i).rank < (incidentVertices A.I).length ∧
    match (T v i).parent with
    | .none => v = A.I.source ∨ (T v i).value = 1
    | .tick j => ∃ h : j < A.d,
        (T v i).value = value A T v (Function.update i ⟨j, h⟩ (i ⟨j, h⟩ + 1))
    | .edge u => (u, v) ∈ callEdges A ∧ u ∈ incidentVertices A.I ∧
        (T v i).value = expectation A T u v i ∧ (T u i).rank < (T v i).rank

theorem constructLayer_parents {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) : TableParents A (constructLayer A T i) i := by
  let S := runQueue A i (incidentVertices A.I).length (initializeLayer A T i)
  have hp : LayerParents A i S := runQueue_parents A i _ _ (initializeLayer_parents A T i)
    (incident_nodup A.I) (fun _ h => h)
  have hs : LayerSync A i S := runQueue_sync A i _ _ (initializeLayer_sync A i T)
  have hq : S.queue = [] := constructLayer_queue_empty A T i
  have hr : S.nextRank ≤ (incidentVertices A.I).length := by
    have hh := runQueue_rank_le A i (incidentVertices A.I).length (initializeLayer A T i)
    change S.nextRank ≤ 0 + (incidentVertices A.I).length at hh
    simpa only [Nat.zero_add] using hh
  change TableParents A S.table i
  intro v hv
  have hn : v ∉ S.queue := by rw [hq]; simp
  change (S.table v i).rank < _ ∧ _
  refine ⟨(hp.rank v hv hn).trans_le hr, ?_⟩
  rw [hp.sync v hv hn]
  have hvalid := hp.valid v hv
  unfold KeyParent at hvalid
  change (match S.parents v with
    | .none => _
    | .tick j => _
    | .edge u => _)
  rw [hs v hv hn]
  cases he : S.parents v with
  | none => simpa [he] using hvalid
  | tick j => simpa [he] using hvalid
  | edge u =>
    rw [he] at hvalid
    exact ⟨hvalid.1, hvalid.2.1, hvalid.2.2.2, hp.before v hv hn u he⟩

theorem constructTable_parents {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) : TableParents A (constructTable A) i := by
  obtain ⟨T, hT, he⟩ := constructTable_layer_witness A hδ hL i hi
  have hp := constructLayer_parents A T i
  intro v hv
  rw [he v i le_rfl]
  have hvp := hp v hv
  refine ⟨hvp.1, ?_⟩
  cases hc : (constructLayer A T i v i).parent with
  | none => simpa only [hc] using hvp.2
  | tick j =>
    rw [hc] at hvp
    obtain ⟨hj, hh⟩ := hvp.2
    refine ⟨hj, ?_⟩
    have hu : ∀ r, i r ≤ Function.update i ⟨j, hj⟩ (i ⟨j, hj⟩ + 1) r := by
      intro r
      by_cases hr : r = ⟨j, hj⟩
      · subst r; simp
      · simp [Function.update_of_ne hr]
    rw [value_congr_vertex A (constructTable A) (constructLayer A T i) v _
      (he v _ (vectorIndex_le _ _ hu))]
    exact hh
  | edge u =>
    rw [hc] at hvp
    have hcon : expectation A (constructTable A) u v i =
        expectation A (constructLayer A T i) u v i := by
      apply expectation_congr
      intro a ha
      exact value_congr_vertex A _ _ u _
        (he u _ (vectorIndex_le _ _ (fun r => Nat.le_add_right _ _)))
    dsimp only
    rw [hcon, he u i le_rfl]
    exact hvp.2

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace RSP.Barrier

theorem log_gap_lower {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (1 - z) ^ 2 / 2 ≤ Real.log z + 1 / z - 1 := by
  let f : ℝ → ℝ := fun x => Real.log x + 1 / x - 1 - (1 - x) ^ 2 / 2
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt f (1 / x - 1 / x ^ 2 + (1 - x)) x := by
    have hlog := Real.hasDerivAt_log (ne_of_gt hx)
    have hinv := (hasDerivAt_id x).inv (ne_of_gt hx)
    have hsq := (((hasDerivAt_id x).const_sub 1).pow 2).div_const 2
    convert! ((hlog.add hinv).sub_const 1).sub hsq using 1
    · ext y
      simp [f, one_div]
    · simp [one_div]
      ring
  have hanti : AntitoneOn f (Set.Icc z 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc z 1)
    · intro x hx
      exact (hd x (lt_of_lt_of_le hz hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (lt_of_lt_of_le hz (interior_subset hx).1)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc z 1 := interior_subset hx
      have hx0 : 0 < x := lt_of_lt_of_le hz hx'.1
      rw [(hd x hx0).deriv]
      have heq : (1 / x - 1 / x ^ 2 + (1 - x)) * x ^ 2 =
          -(1 - x) * (1 - x ^ 2) := by
        field_simp [ne_of_gt hx0]
        <;> ring
      have hsq : x ^ 2 ≤ 1 := by nlinarith [hx'.2]
      have hp := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hx'.2))
        (sub_nonneg.mpr hsq)
      rw [← heq] at hp
      nlinarith [sq_pos_of_pos hx0]
  have h := hanti ⟨le_rfl, hz1⟩ ⟨hz1, le_rfl⟩ hz1
  simp only [f, Real.log_one, div_one, sub_self, zero_pow (by decide : 2 ≠ 0),
    zero_div, add_zero, sub_zero] at h
  linarith

theorem k_clock_barrier {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k q : ℕ) (hk : 1 ≤ k) (hq : 512 * (k : ℝ) / δ ^ 2 ≤ (q : ℝ)) :
    let z := (1 + δ / 2) / (1 + δ)
    8 * (k : ℝ) ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) := by
  let z := (1 + δ / 2) / (1 + δ)
  change 8 * (k : ℝ) ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z)
  have hd : 0 < 1 + δ := by linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ hd).mpr
    linarith
  have hgap : δ / 4 ≤ 1 - z := by
    have heq : 1 - z = (δ / 2) / (1 + δ) := by
      dsimp [z]
      field_simp [ne_of_gt hd]
      <;> ring
    rw [heq]
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (le_of_lt hδ) (sub_nonneg.mpr hδ1)]
  have hlog : δ ^ 2 / 32 ≤ Real.log z + 1 / z - 1 := by
    have h := log_gap_lower hz hz1
    nlinarith [sq_nonneg (1 - z - δ / 4)]
  have hqδ : 512 * (k : ℝ) ≤ (q : ℝ) * δ ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hδ)).mp hq
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq1r : (1 : ℝ) ≤ q := by
    have hd2 : δ ^ 2 ≤ 1 := by nlinarith
    have hn : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hq1 : 1 ≤ q := by exact_mod_cast hq1r
  have hprod : 16 * (k : ℝ) ≤ (q : ℝ) * (Real.log z + 1 / z - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith
  have hlog0 : Real.log z ≤ 0 := Real.log_nonpos (le_of_lt hz) hz1
  have hexp : 16 * (k : ℝ) ≤
      ((q - 1 : ℕ) : ℝ) * Real.log z + (q : ℝ) * (1 - z) / z := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
    have heq : ((q : ℝ) - 1) * Real.log z + (q : ℝ) * (1 - z) / z =
        (q : ℝ) * (Real.log z + 1 / z - 1) - Real.log z := by
      field_simp
      <;> ring
    rw [heq]
    linarith
  calc
    8 * (k : ℝ) ≤ Real.exp (16 * (k : ℝ)) := by
      nlinarith [Real.add_one_le_exp (16 * (k : ℝ))]
    _ ≤ Real.exp (((q - 1 : ℕ) : ℝ) * Real.log z + (q : ℝ) * (1 - z) / z) :=
      Real.exp_le_exp.mpr hexp
    _ = z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hz]

end RSP.Barrier

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

namespace NearLinearRSP.TwoResources.Supplement

theorem weighted_minimum {α : Type} (xs : List α) (hxs : xs ≠ [])
    (fallback : α) (p score : α → ℝ) (P : ℝ)
    (hp : ∀ a ∈ xs, 0 ≤ p a) (hpsum : (xs.map p).sum ≤ 1)
    (hbound : 1 - (xs.map p).sum + (xs.map (fun a => p a * score a)).sum ≤ P)
    (hP : P < 1) : score (selectMin score xs fallback) ≤ P := by
  have h0 : 0 ≤ (xs.map p).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    exact hp a ha
  have hmin (a : α) (ha : a ∈ xs) := selectMin_le_mem score xs fallback a ha
  have hsum : (xs.map p).sum * score (selectMin score xs fallback) ≤
      (xs.map (fun a => p a * score a)).sum := by
    rw [← List.sum_map_mul_right]
    apply List.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (hmin a ha) (hp a ha)
  by_contra hn
  have hn' : P < score (selectMin score xs fallback) := lt_of_not_ge hn
  by_cases hz : (xs.map p).sum = 0
  · rw [hz] at hsum hbound
    norm_num at hsum hbound
    linarith
  · have hp0 : 0 < (xs.map p).sum := lt_of_le_of_ne h0 (Ne.symm hz)
    have ha := mul_nonneg (sub_nonneg.mpr hpsum) (sub_nonneg.mpr hP.le)
    have hb := mul_pos hp0 (sub_pos.mpr hn')
    nlinarith

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
open scoped NNReal BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem prod_exp_resource {α : Type*} (xs : List α) (w : α → ℝ) (r z : ℝ) :
    (xs.map (fun x => Real.exp (r * w x * (z - 1)))).prod =
      Real.exp (r * (xs.map w).sum * (z - 1)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih, ← Real.exp_add]
    congr 1
    ring

theorem clockPGF_prod {k : ℕ} (A : ClockCall k) (j : Fin A.d) (P : List ℕ) :
    ((P.zip P.tail).map (fun e => clockPGF A j e.1 e.2)).prod =
      Real.exp (clockRate A j * pathWeight (coordinateWeight A.I (A.coords.get j)) P *
        (clockZ A - 1)) := by
  exact prod_exp_resource (P.zip P.tail)
    (fun e => (coordinateWeight A.I (A.coords.get j) e.1 e.2 : ℝ))
    (clockRate A j) (clockZ A)

theorem clockPGF_prod_pos {k : ℕ} (A : ClockCall k) (j : Fin A.d) (P : List ℕ) :
    0 < ((P.zip P.tail).map (fun e => clockPGF A j e.1 e.2)).prod := by
  rw [clockPGF_prod]
  exact Real.exp_pos _

theorem resource_term_barrier {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k q : ℕ) (hk : 1 ≤ k) (hq : 512 * (k : ℝ) / δ ^ 2 ≤ (q : ℝ))
    (i : ℕ) (hi : i < q) (a : ℝ)
    (ha : (q : ℝ) / ((1 + δ / 2) / (1 + δ)) ≤ a) :
    let z := (1 + δ / 2) / (1 + δ)
    1 ≤ z ^ i / (8 * (k : ℝ) * Real.exp (a * (z - 1))) := by
  let z := (1 + δ / 2) / (1 + δ)
  change 1 ≤ z ^ i / (8 * (k : ℝ) * Real.exp (a * (z - 1)))
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ (by linarith : 0 < 1 + δ)).mpr
    linarith
  have hp : z ^ (q - 1) ≤ z ^ i :=
    pow_le_pow_of_le_one hz.le hz1 (by omega)
  have he : (q : ℝ) * (1 - z) / z ≤ a * (1 - z) := by
    simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hz1)
  have hbig : 8 * (k : ℝ) ≤ z ^ i * Real.exp (a * (1 - z)) := by
    calc
      8 * (k : ℝ) ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) :=
        RSP.Barrier.k_clock_barrier hδ hδ1 k q hk hq
      _ ≤ z ^ i * Real.exp (a * (1 - z)) :=
        mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (pow_nonneg hz.le i)
  have heq : Real.exp (a * (1 - z)) = (Real.exp (a * (z - 1)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [heq] at hbig
  apply (le_div_iff₀ (by positivity : 0 < 8 * (k : ℝ) * Real.exp (a * (z - 1)))).mpr
  have h := (le_div_iff₀ (Real.exp_pos (a * (z - 1)))).mp
    (show 8 * (k : ℝ) ≤ z ^ i / Real.exp (a * (z - 1)) by
      simpa [div_eq_mul_inv] using hbig)
  simpa using h

theorem normalized_resource_barrier {k : ℕ} (A : ClockCall k)
    (hk : 1 ≤ k) (hδ : 0 < A.δ) (hδ1 : A.δ ≤ 1)
    (B w : ℝ) (hB : 0 < B) (hw : (1 + A.δ) * B ≤ w)
    (i : ℕ) (hi : i < A.q) :
    1 ≤ clockZ A ^ i /
      (8 * (k : ℝ) * Real.exp (((A.q : ℝ) / ((1 + A.δ / 2) * B)) * w * (clockZ A - 1))) := by
  have hhalf : 0 < 1 + A.δ / 2 := by linarith
  have hwhole : 0 < 1 + A.δ := by linarith
  have ha : (A.q : ℝ) / clockZ A ≤ (A.q : ℝ) / ((1 + A.δ / 2) * B) * w := by
    calc
      (A.q : ℝ) / clockZ A =
          (A.q : ℝ) / ((1 + A.δ / 2) * B) * ((1 + A.δ) * B) := by
        unfold clockZ
        field_simp
        <;> ring
      _ ≤ (A.q : ℝ) / ((1 + A.δ / 2) * B) * w :=
        mul_le_mul_of_nonneg_left hw (by positivity)
  exact resource_term_barrier hδ hδ1 k A.q hk (Nat.le_ceil _) i hi _ ha

theorem potential_coeff_nonneg {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ)
    (i : Fin A.d → ℕ) (P : List ℕ) (j : Fin A.d) :
    0 ≤ clockZ A ^ i j /
      (8 * (k : ℝ) * ((P.zip P.tail).map (fun e => clockPGF A j e.1 e.2)).prod) := by
  apply div_nonneg (pow_nonneg (clockZ_pos A hδ).le _)
  exact mul_nonneg (by positivity) (clockPGF_prod_pos A j P).le

theorem potential_unsaturated {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ)
    (T : MultiTable A.d) (v : ℕ) (i : Fin A.d → ℕ) (P : List ℕ)
    (hΦ : multiPotential A T v i P < 1) : ∀ j, i j < A.q := by
  have hsum : 0 ≤ ∑ j : Fin A.d, clockZ A ^ i j /
      (8 * (k : ℝ) * ((P.zip P.tail).map (fun e => clockPGF A j e.1 e.2)).prod) :=
    Finset.sum_nonneg (fun j _ => potential_coeff_nonneg A hδ i P j)
  intro j
  by_contra hj
  have hsat := value_of_saturated A T v i ⟨j, le_of_not_gt hj⟩
  unfold multiPotential at hΦ
  rw [hsat] at hΦ
  linarith

theorem potential_coordinate_bound {k : ℕ} (A : ClockCall k)
    (hk : 1 ≤ k) (hδ : 0 < A.δ) (hδ1 : A.δ ≤ 1) (hL : 0 < A.L)
    (T : MultiTable A.d) (hT : MultiRange T) (v : ℕ) (i : Fin A.d → ℕ) (P : List ℕ)
    (hΦ : multiPotential A T v i P < 1) (j : Fin A.d) :
    pathWeight (coordinateWeight A.I (A.coords.get j)) P ≤
      (1 + A.δ) * coordinateBudget A.I A.L (A.coords.get j) := by
  have hi := potential_unsaturated A hδ T v i P hΦ j
  have hB := clockBudget_pos A.I A.L hL j
  by_contra hw
  have hw' : (1 + A.δ) * coordinateBudget A.I A.L (A.coords.get j) ≤
      pathWeight (coordinateWeight A.I (A.coords.get j)) P := (lt_of_not_ge hw).le
  have hbar := normalized_resource_barrier A hk hδ hδ1
    (coordinateBudget A.I A.L (A.coords.get j))
    (pathWeight (coordinateWeight A.I (A.coords.get j)) P) hB hw' (i j) hi
  have hsingle := Finset.single_le_sum
    (fun r (_ : r ∈ (Finset.univ : Finset (Fin A.d))) => potential_coeff_nonneg A hδ i P r)
    (Finset.mem_univ j)
  have hD := (value_range A T hT v i).1
  unfold multiPotential at hΦ
  rw [clockPGF_prod] at hsingle
  change clockZ A ^ i j /
      (8 * (k : ℝ) * Real.exp (((A.q : ℝ) /
        ((1 + A.δ / 2) * coordinateBudget A.I A.L (A.coords.get j))) *
        pathWeight (coordinateWeight A.I (A.coords.get j)) P * (clockZ A - 1))) ≤ _ at hsingle
  linarith

theorem initial_potential_bound {k : ℕ} (A : ClockCall k) (hk : 1 ≤ k) (t : ℕ)
    (ha : accepts A t = true) :
    multiPotential A (constructTable A) t (fun _ => 0) [t] < 1 := by
  have hd : (A.d : ℝ) ≤ k := by
    exact_mod_cast clockCoordinates_length_le A.I
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hsum : (A.d : ℝ) * (1 / (8 * (k : ℝ))) ≤ 1 / 8 := by
    calc
      (A.d : ℝ) * (1 / (8 * (k : ℝ))) ≤ (k : ℝ) * (1 / (8 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ = 1 / 8 := by field_simp
  have hv : value A (constructTable A) t (fun _ => 0) ≤ 1 / 4 := by
    simpa only [accepts, decide_eq_true_eq] using ha
  simp only [multiPotential, List.tail_cons, List.zip_nil_right, List.map_nil, List.prod_nil,
    pow_zero, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem list_sum_fin_sum {α : Type*} {d : ℕ} (xs : List α) (f : α → Fin d → ℝ) :
    (xs.map (fun a => ∑ r, f a r)).sum = ∑ r, (xs.map (fun a => f a r)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Finset.sum_add_distrib]

theorem rectangle_pgf_le {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (u v : ℕ) (i : Fin A.d → ℕ) (j : Fin A.d) :
    ((rectangle A i).map (fun a => incrementMass A u v a * clockZ A ^ a j)).sum ≤
      clockPGF A j u v := by
  classical
  have hp := incrementMass_pgf_hasSum A hδ hL u v j
  have hh := sum_le_hasSum (rectangle A i).toFinset
    (fun a ha => mul_nonneg (incrementMass_nonneg A hδ hL u v a)
      (pow_nonneg (clockZ_pos A hδ).le _)) hp
  simpa only [List.sum_toFinset _ (rectangle_nodup A i)] using hh

theorem incrementScore_average_le {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (S : RetrievalState A.d) (hH : ∀ r, 0 ≤ S.H r) (u v : ℕ) :
    1 - ((rectangle A S.counts).map (incrementMass A u v)).sum +
      ((rectangle A S.counts).map
        (fun a => incrementMass A u v a * incrementScore A T S u v a)).sum ≤
      expectation A T u v S.counts + ∑ r, S.H r := by
  have hm (r : Fin A.d) :
      ((rectangle A S.counts).map (fun a =>
        incrementMass A u v a * (clockZ A ^ a r * S.H r / clockPGF A r u v))).sum ≤
        S.H r := by
    have hpgf := clockPGF_pos A r u v
    have hcoef : 0 ≤ S.H r / clockPGF A r u v := div_nonneg (hH r) hpgf.le
    calc
      _ = ((rectangle A S.counts).map
          (fun a => incrementMass A u v a * clockZ A ^ a r)).sum *
            (S.H r / clockPGF A r u v) := by
        rw [← List.sum_map_mul_right]
        congr 1
        apply List.map_congr_left
        intro a ha
        ring
      _ ≤ clockPGF A r u v * (S.H r / clockPGF A r u v) :=
        mul_le_mul_of_nonneg_right (rectangle_pgf_le A hδ hL u v S.counts r) hcoef
      _ = S.H r := by field_simp
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin A.d))) => hm r)
  simp only [incrementScore, mul_add, Finset.mul_sum, List.sum_map_add,
    list_sum_fin_sum]
  unfold expectation
  linarith

theorem incrementScore_minimum_le {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (S : RetrievalState A.d) (hH : ∀ r, 0 ≤ S.H r)
    (hi : ∀ r, S.counts r < A.q) (u v : ℕ) (P : ℝ)
    (hbound : expectation A T u v S.counts + ∑ r, S.H r ≤ P) (hP : P < 1)
    (fallback : Fin A.d → ℕ) :
    incrementScore A T S u v
      (selectMin (incrementScore A T S u v) (rectangle A S.counts) fallback) ≤ P := by
  exact weighted_minimum (rectangle A S.counts) (rectangle_ne_nil A S.counts hi)
    fallback (incrementMass A u v) (incrementScore A T S u v) P
    (fun a ha => incrementMass_nonneg A hδ hL u v a)
    (rectangle_mass_le_one A hδ hL u v S.counts)
    ((incrementScore_average_le A hδ hL T S hH u v).trans hbound) hP

def Coefficients {k : ℕ} (A : ClockCall k) (S : RetrievalState A.d) : Prop :=
  ∀ r, S.H r = clockZ A ^ S.counts r /
    (8 * (k : ℝ) * ((S.path.zip S.path.tail).map (fun e => clockPGF A r e.1 e.2)).prod)

theorem coefficients_initial {k : ℕ} (A : ClockCall k) (t : ℕ) :
    Coefficients A ⟨[t], fun _ => 0, fun _ => 1 / (8 * (k : ℝ))⟩ := by
  intro r
  simp

theorem coefficients_nonneg {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ)
    (S : RetrievalState A.d) (hS : Coefficients A S) : ∀ r, 0 ≤ S.H r := by
  intro r
  rw [hS r]
  exact potential_coeff_nonneg A hδ S.counts S.path r

theorem coefficients_potential {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (S : RetrievalState A.d) (hS : Coefficients A S) (v : ℕ) :
    multiPotential A T v S.counts S.path = value A T v S.counts + ∑ r, S.H r := by
  unfold multiPotential
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact (hS r).symm

theorem coefficients_tick {k : ℕ} (A : ClockCall k) (S : RetrievalState A.d)
    (hS : Coefficients A S) (j : Fin A.d) :
    Coefficients A { S with
      counts := Function.update S.counts j (S.counts j + 1)
      H := Function.update S.H j (clockZ A * S.H j) } := by
  intro r
  by_cases hr : r = j
  · subst r
    simp only [Function.update_self]
    rw [hS j, pow_succ]
    ring
  · simpa only [Function.update_of_ne hr] using hS r

theorem coefficients_edge {k : ℕ} (A : ClockCall k) (S : RetrievalState A.d)
    (hS : Coefficients A S) (u v : ℕ) (hv : S.path.head? = some v)
    (a : Fin A.d → ℕ) :
    Coefficients A ⟨u :: S.path, (fun r => S.counts r + a r),
      (fun r => clockZ A ^ a r * S.H r / clockPGF A r u v)⟩ := by
  intro r
  cases hp : S.path with
  | nil => simp [hp] at hv
  | cons w ws =>
    have hw : w = v := by simpa [hp] using hv
    subst w
    simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.prod_cons]
    rw [hS r, pow_add, hp]
    simp only [List.tail_cons]
    ring

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement

noncomputable def clockMeasure {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) : ℕ :=
  (A.d * A.q - ∑ r, i r) * ((incidentVertices A.I).length + 1) + (T v i).rank + 1

theorem clockMeasure_pos {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) : 0 < clockMeasure A T v i := by
  unfold clockMeasure
  omega

theorem counts_sum_le {d q : ℕ} (i : Fin d → ℕ) (hi : ∀ r, i r < q) :
    ∑ r, i r ≤ d * q := by
  calc
    _ ≤ ∑ _r : Fin d, q := Finset.sum_le_sum (fun r _ => (hi r).le)
    _ = _ := by simp

theorem counts_sum_lt {d : ℕ} (i j : Fin d → ℕ)
    (hle : ∀ r, i r ≤ j r) (hne : i ≠ j) : (∑ r, i r) < ∑ r, j r := by
  classical
  apply Finset.sum_lt_sum (fun r _ => hle r)
  by_contra hn
  push Not at hn
  apply hne
  funext r
  exact Nat.le_antisymm (hle r) (hn r (Finset.mem_univ r))

theorem clockMeasure_lt_of_counts {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (u v : ℕ) (i j : Fin A.d → ℕ) (hj : ∀ r, j r < A.q)
    (hle : ∀ r, i r ≤ j r) (hne : i ≠ j)
    (hrank : (T u j).rank < (incidentVertices A.I).length) :
    clockMeasure A T u j < clockMeasure A T v i := by
  have hs := counts_sum_lt i j hle hne
  have hj' := counts_sum_le j hj
  have hrem : (A.d * A.q - ∑ r, j r) + 1 ≤ A.d * A.q - ∑ r, i r := by omega
  have hm := Nat.mul_le_mul_right ((incidentVertices A.I).length + 1) hrem
  rw [Nat.add_mul, Nat.one_mul] at hm
  unfold clockMeasure
  omega

theorem clockMeasure_lt_of_rank {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (u v : ℕ) (i : Fin A.d → ℕ) (hrank : (T u i).rank < (T v i).rank) :
    clockMeasure A T u i < clockMeasure A T v i := by
  unfold clockMeasure
  omega

theorem clockMeasure_initial_bound {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (hrank : (T v (fun _ => 0)).rank < (incidentVertices A.I).length) :
    clockMeasure A T v (fun _ => 0) ≤
      (A.d * A.q + 1) * ((incidentVertices A.I).length + 1) + 1 := by
  simp only [clockMeasure, Finset.sum_const_zero, Nat.sub_zero, Nat.add_mul, Nat.one_mul]
  omega

theorem tick_potential_le {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ)
    (T : MultiTable A.d) (S : RetrievalState A.d) (hS : Coefficients A S)
    (v : ℕ) (j : Fin A.d)
    (he : value A T v S.counts = value A T v (Function.update S.counts j (S.counts j + 1))) :
    multiPotential A T v (Function.update S.counts j (S.counts j + 1)) S.path ≤
      multiPotential A T v S.counts S.path := by
  let U : RetrievalState A.d := { S with
    counts := Function.update S.counts j (S.counts j + 1)
    H := Function.update S.H j (clockZ A * S.H j) }
  have hU : Coefficients A U := coefficients_tick A S hS j
  have hsum : (∑ r, U.H r) ≤ ∑ r, S.H r := by
    apply Finset.sum_le_sum
    intro r hr
    by_cases heq : r = j
    · subst r
      change Function.update S.H j (clockZ A * S.H j) j ≤ S.H j
      rw [Function.update_self]
      exact mul_le_of_le_one_left (coefficients_nonneg A hδ S hS j) (clockZ_lt_one A hδ).le
    · simp [U, Function.update_of_ne heq]
  change multiPotential A T v U.counts U.path ≤ multiPotential A T v S.counts S.path
  rw [coefficients_potential A T U hU v, coefficients_potential A T S hS v]
  change value A T v (Function.update S.counts j (S.counts j + 1)) + _ ≤ _
  rw [← he]
  linarith

theorem edge_potential_le {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (S : RetrievalState A.d) (hS : Coefficients A S)
    (u v : ℕ) (hv : S.path.head? = some v)
    (he : value A T v S.counts = expectation A T u v S.counts)
    (hP : multiPotential A T v S.counts S.path < 1)
    (fallback : Fin A.d → ℕ) :
    let a := selectMin (incrementScore A T S u v) (rectangle A S.counts) fallback
    multiPotential A T u (fun r => S.counts r + a r) (u :: S.path) ≤
      multiPotential A T v S.counts S.path := by
  let a := selectMin (incrementScore A T S u v) (rectangle A S.counts) fallback
  let U : RetrievalState A.d := ⟨u :: S.path, (fun r => S.counts r + a r),
    (fun r => clockZ A ^ a r * S.H r / clockPGF A r u v)⟩
  have hU : Coefficients A U := coefficients_edge A S hS u v hv a
  have hi := potential_unsaturated A hδ T v S.counts S.path hP
  have hmin := incrementScore_minimum_le A hδ hL T S (coefficients_nonneg A hδ S hS)
    hi u v (multiPotential A T v S.counts S.path) ?_ hP fallback
  · change multiPotential A T u U.counts U.path ≤ _
    rw [coefficients_potential A T U hU u]
    exact hmin
  · rw [coefficients_potential A T S hS v, he]

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem retrieveFuel_success {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (fuel : ℕ) (S : RetrievalState A.d)
    (v : ℕ) (hhead : S.path.head? = some v) (hv : v ∈ incidentVertices A.I)
    (hchain : S.path.IsChain (fun u v => (u, v) ∈ callEdges A))
    (hcoeff : Coefficients A S)
    (hP : multiPotential A (constructTable A) v S.counts S.path < 1)
    (hf : clockMeasure A (constructTable A) v S.counts ≤ fuel) :
    ∃ P : List ℕ, ∃ j : Fin A.d → ℕ,
      retrieveFuel A (constructTable A) fuel S = some P ∧
      P.head? = some A.I.source ∧ P.getLast? = S.path.getLast? ∧
      P.IsChain (fun u v => (u, v) ∈ callEdges A) ∧
      multiPotential A (constructTable A) A.I.source j P < 1 := by
  induction fuel generalizing S v with
  | zero =>
    have hp := clockMeasure_pos A (constructTable A) v S.counts
    omega
  | succ fuel ih =>
    have hi := potential_unsaturated A hδ (constructTable A) v S.counts S.path hP
    have hn : ¬∃ r, A.q ≤ S.counts r := by
      rintro ⟨r, hr⟩
      exact (Nat.not_le.mpr (hi r)) hr
    rw [retrieveFuel, if_neg hn, hhead]
    dsimp only
    by_cases hs : v = A.I.source
    · rw [if_pos hs]
      refine ⟨S.path, S.counts, rfl, ?_, rfl, hchain, ?_⟩
      · simpa only [hs] using hhead
      · simpa only [hs] using hP
    · rw [if_neg hs]
      have hpar := (constructTable_parents A hδ hL S.counts hi v hv).2
      cases hp : (constructTable A v S.counts).parent with
      | none =>
        rw [hp] at hpar
        rcases hpar with hh | hh
        · exact (hs hh).elim
        · have hz := Finset.sum_nonneg
            (fun r (_ : r ∈ (Finset.univ : Finset (Fin A.d))) =>
              coefficients_nonneg A hδ S hcoeff r)
          rw [coefficients_potential A (constructTable A) S hcoeff v,
            value_of_valid A (constructTable A) v S.counts hi, hh] at hP
          linarith
      | tick j =>
        rw [hp] at hpar
        obtain ⟨hj, he⟩ := hpar
        dsimp only
        rw [dif_pos hj]
        let r : Fin A.d := ⟨j, hj⟩
        let U : RetrievalState A.d := { S with
          counts := Function.update S.counts r (S.counts r + 1)
          H := Function.update S.H r (clockZ A * S.H r) }
        have hc : Coefficients A U := coefficients_tick A S hcoeff r
        have he' : value A (constructTable A) v S.counts =
            value A (constructTable A) v U.counts := by
          rw [value_of_valid A (constructTable A) v S.counts hi]
          exact he
        have hP' : multiPotential A (constructTable A) v U.counts U.path < 1 :=
          (tick_potential_le A hδ (constructTable A) S hcoeff v r he').trans_lt hP
        have hi' := potential_unsaturated A hδ (constructTable A) v U.counts U.path hP'
        have hle : ∀ a, S.counts a ≤ U.counts a := by
          intro a
          by_cases ha : a = r
          · subst a; simp [U]
          · simp [U, Function.update_of_ne ha]
        have hne : S.counts ≠ U.counts := (tick_index_ne S.counts r).symm
        have hm := clockMeasure_lt_of_counts A (constructTable A) v v S.counts U.counts hi' hle hne
          (constructTable_parents A hδ hL U.counts hi' v hv).1
        have hf' : clockMeasure A (constructTable A) v U.counts ≤ fuel := by omega
        obtain ⟨P, c, hret, hstart, hlast, hchain', hpot⟩ :=
          ih U v hhead hv hchain hc hP' hf'
        exact ⟨P, c, hret, hstart, hlast, hchain', hpot⟩
      | edge u =>
        rw [hp] at hpar
        have hnonempty := rectangle_ne_nil A S.counts hi
        cases hr : rectangle A S.counts with
        | nil => exact (hnonempty hr).elim
        | cons a rest =>
          let b := selectMin (incrementScore A (constructTable A) S u v) (a :: rest) a
          let U : RetrievalState A.d := ⟨u :: S.path, (fun r => S.counts r + b r),
            (fun r => clockZ A ^ b r * S.H r / clockPGF A r u v)⟩
          have hb : b ∈ rectangle A S.counts := by
            rw [hr]
            exact selectMin_mem _ _ _ (List.cons_ne_nil _ _)
          have hi' : ∀ r, U.counts r < A.q := (rectangle_mem A S.counts b).mp hb
          have hc : Coefficients A U := coefficients_edge A S hcoeff u v hhead b
          have he : value A (constructTable A) v S.counts =
              expectation A (constructTable A) u v S.counts := by
            rw [value_of_valid A (constructTable A) v S.counts hi]
            exact hpar.2.2.1
          have hP' : multiPotential A (constructTable A) u U.counts U.path < 1 := by
            have hh := edge_potential_le A hδ hL (constructTable A) S hcoeff u v hhead he hP a
            rw [hr] at hh
            exact hh.trans_lt hP
          have hm : clockMeasure A (constructTable A) u U.counts <
              clockMeasure A (constructTable A) v S.counts := by
            by_cases hb0 : b = (fun _ => 0)
            · simpa only [U, hb0, Nat.add_zero] using
                clockMeasure_lt_of_rank A (constructTable A) u v S.counts hpar.2.2.2
            · have hle : ∀ r, S.counts r ≤ U.counts r := fun r => Nat.le_add_right _ _
              have hne : S.counts ≠ U.counts := by
                intro h
                apply hb0
                funext r
                have hh := congrFun h r
                dsimp [U] at hh
                omega
              exact clockMeasure_lt_of_counts A (constructTable A) u v S.counts U.counts hi' hle hne
                (constructTable_parents A hδ hL U.counts hi' u hpar.2.1).1
          have hf' : clockMeasure A (constructTable A) u U.counts ≤ fuel := by omega
          have hchainU : U.path.IsChain (fun u v => (u, v) ∈ callEdges A) := by
            apply hchain.cons
            intro w hw
            have hw' : w = v := (show v = w from by simpa only [hhead, Option.mem_some_iff] using hw).symm
            subst w
            exact hpar.1
          have hlastU : U.path.getLast? = S.path.getLast? := by
            cases hp' : S.path with
            | nil => simp [hp'] at hhead
            | cons w ws => simp [U, hp']
          obtain ⟨P, c, hret, hstart, hlast, hchain', hpot⟩ :=
            ih U u rfl hpar.2.1 hchainU hc hP' hf'
          exact ⟨P, c, hret, hstart, hlast.trans hlastU, hchain', hpot⟩

theorem retrieve_success {k : ℕ} (A : ClockCall k) (hk : 1 ≤ k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (t : ℕ) (ht : t ∈ incidentVertices A.I)
    (ha : accepts A t = true) :
    ∃ P : List ℕ, ∃ j : Fin A.d → ℕ,
      retrieve A t = some P ∧ P.head? = some A.I.source ∧ P.getLast? = some t ∧
      P.IsChain (fun u v => (u, v) ∈ callEdges A) ∧
      multiPotential A (constructTable A) A.I.source j P < 1 := by
  have hP := initial_potential_bound A hk t ha
  have hi := potential_unsaturated A hδ (constructTable A) t (fun _ => 0) [t] hP
  exact retrieveFuel_success A hδ hL _ _ t rfl ht (List.isChain_singleton t)
    (coefficients_initial A t) hP
    (clockMeasure_initial_bound A (constructTable A) t
      (constructTable_parents A hδ hL (fun _ => 0) hi t ht).1)

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement

noncomputable def tickState {k : ℕ} (A : ClockCall k) (S : RetrievalState A.d)
    (r : Fin A.d) : RetrievalState A.d :=
  { S with counts := Function.update S.counts r (S.counts r + 1),
           H := Function.update S.H r (clockZ A * S.H r) }

noncomputable def edgeState {k : ℕ} (A : ClockCall k) (S : RetrievalState A.d)
    (u v : ℕ) (b : Fin A.d → ℕ) : RetrievalState A.d :=
  ⟨u :: S.path, (fun r => S.counts r + b r),
    fun r => clockZ A ^ b r * S.H r / clockPGF A r u v⟩

inductive Backtrace {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) :
    RetrievalState A.d → List ℕ → ℕ → ℕ → Prop where
  | source (S : RetrievalState A.d) (valid : ∀ r, S.counts r < A.q)
      (head : S.path.head? = some A.I.source) : Backtrace A T S S.path 0 0
  | tick {S : RetrievalState A.d} {P : List ℕ} {ticks edges v j : ℕ}
      (valid : ∀ r, S.counts r < A.q) (head : S.path.head? = some v) (away : v ≠ A.I.source)
      (parent : (T v S.counts).parent = .tick j) (hj : j < A.d)
      (tail : Backtrace A T (tickState A S ⟨j, hj⟩) P ticks edges) :
      Backtrace A T S P (ticks + 1) edges
  | edge {S : RetrievalState A.d} {P : List ℕ} {ticks edges u v : ℕ}
      {a : Fin A.d → ℕ} {rest : List (Fin A.d → ℕ)}
      (valid : ∀ r, S.counts r < A.q) (head : S.path.head? = some v) (away : v ≠ A.I.source)
      (parent : (T v S.counts).parent = .edge u) (box : rectangle A S.counts = a :: rest)
      (tail : Backtrace A T
        (edgeState A S u v (selectMin (incrementScore A T S u v) (a :: rest) a)) P ticks edges) :
      Backtrace A T S P ticks (edges + 1)

theorem retrieveFuel_backtrace {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (fuel : ℕ) (S : RetrievalState A.d) (P : List ℕ) (hs : retrieveFuel A T fuel S = some P) :
    ∃ ticks edges, Backtrace A T S P ticks edges ∧ ticks + edges + 1 ≤ fuel := by
  induction fuel generalizing S with
  | zero => simp [retrieveFuel] at hs
  | succ fuel ih =>
    by_cases hbad : ∃ r, A.q ≤ S.counts r
    · simp [retrieveFuel, hbad] at hs
    have hi : ∀ r, S.counts r < A.q := fun r => Nat.lt_of_not_ge (fun hr => hbad ⟨r, hr⟩)
    rw [retrieveFuel, if_neg hbad] at hs
    cases hh : S.path.head? with
    | none => simp [hh] at hs
    | some v =>
      rw [hh] at hs
      by_cases hv : v = A.I.source
      · subst v
        simp at hs
        subst P
        exact ⟨0, 0, .source S hi hh, by omega⟩
      · simp only [if_neg hv] at hs
        cases hp : (T v S.counts).parent with
        | none => simp [hp] at hs
        | tick j =>
          rw [hp] at hs
          by_cases hj : j < A.d
          · simp only [dif_pos hj] at hs
            obtain ⟨b, e, htail, hlen⟩ := ih (tickState A S ⟨j, hj⟩) hs
            exact ⟨b + 1, e, .tick hi hh hv hp hj htail, by omega⟩
          · simp [hj] at hs
        | edge u =>
          rw [hp] at hs
          cases hr : rectangle A S.counts with
          | nil => simp [hr] at hs
          | cons a rest =>
            simp only [hr] at hs
            obtain ⟨b, e, htail, hlen⟩ := ih
              (edgeState A S u v (selectMin (incrementScore A T S u v) (a :: rest) a)) hs
            exact ⟨b, e + 1, .edge hi hh hv hp hr htail, by omega⟩

theorem backtrace_counts {k : ℕ} {A : ClockCall k} {T : MultiTable A.d}
    {S : RetrievalState A.d} {P : List ℕ} {ticks edges : ℕ}
    (h : Backtrace A T S P ticks edges) :
    ticks + (∑ r, S.counts r) ≤ A.d * A.q ∧ P.length = S.path.length + edges := by
  induction h with
  | source S hi hh => exact ⟨by simpa using counts_sum_le S.counts hi, by simp⟩
  | @tick S P t e v j hi hh hv hp hj tail ih =>
    let r : Fin A.d := ⟨j, hj⟩
    let U := tickState A S r
    have hle (x : Fin A.d) : S.counts x ≤ U.counts x := by
      by_cases he : x = r
      · subst x; simp [U, tickState]
      · simp [U, tickState, Function.update_of_ne he]
    have hne : S.counts ≠ U.counts := (tick_index_ne S.counts r).symm
    have hs := counts_sum_lt S.counts U.counts hle hne
    change t + (∑ x, U.counts x) ≤ A.d * A.q ∧ P.length = S.path.length + e at ih
    exact ⟨by omega, ih.2⟩
  | @edge S P t e u v a rest hi hh hv hp hr tail ih =>
    let b := selectMin (incrementScore A T S u v) (a :: rest) a
    have hs : (∑ r, S.counts r) ≤ ∑ r, (S.counts r + b r) :=
      Finset.sum_le_sum (fun r _ => Nat.le_add_right _ _)
    change t + (∑ r, (S.counts r + b r)) ≤ A.d * A.q ∧ P.length = (u :: S.path).length + e at ih
    simp only [List.length_cons] at ih
    exact ⟨by omega, by omega⟩

theorem backtrace_work_bound {k : ℕ} {A : ClockCall k} {T : MultiTable A.d}
    {S : RetrievalState A.d} {P : List ℕ} {ticks edges : ℕ} (hk : 1 ≤ k)
    (h : Backtrace A T S P ticks edges) (c : ℕ) :
    c * (ticks + 1 + (edges + 1) * (A.q + 1) ^ A.d) ≤
      c * ((k + 2) * (A.q + 1) ^ k * (P.length + 1)) := by
  obtain ⟨ht, he⟩ := backtrace_counts h
  have hd : A.d ≤ k := clockCoordinates_length_le A.I
  have hp : (A.q + 1) ^ A.d ≤ (A.q + 1) ^ k := Nat.pow_le_pow_right (by omega) hd
  have hq : A.q + 1 ≤ (A.q + 1) ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n := A.q + 1) (by omega) hk
  have he' : edges + 1 ≤ P.length + 1 := by omega
  have ht' : ticks ≤ k * (A.q + 1) ^ k :=
    (show ticks ≤ A.d * A.q by omega).trans (Nat.mul_le_mul hd (by omega))
  have hp' : 1 ≤ (A.q + 1) ^ k := by omega
  have he'' := Nat.mul_le_mul he' hp
  have hb := Nat.mul_le_mul_left (k * (A.q + 1) ^ k) (show 1 ≤ P.length + 1 by omega)
  have hl := Nat.mul_le_mul_left ((A.q + 1) ^ k) (show 1 ≤ P.length + 1 by omega)
  apply Nat.mul_le_mul_left
  simp only [Nat.mul_one] at hb hl
  rw [Nat.add_mul, Nat.add_mul]
  rw [Nat.mul_comm (P.length + 1)] at he''
  nlinarith

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

theorem scanAddress_tick {d : ℕ} (base n q v : ℕ) (i : Fin d → ℕ) (r : Fin d) :
    scanAddress base n q v (Function.update i r (i r + 1)) =
      scanAddress base n q v i + stride n q r := by
  let e : Fin d → ℕ := fun x => if x = r then 1 else 0
  have h : Function.update i r (i r + 1) = fun x => i x + e x := by
    funext x
    by_cases hx : x = r
    · subst x; simp [e]
    · simp [e, hx]
  have he : vectorIndex q e = q ^ (d - 1 - r.val) := by simp [vectorIndex, e, ite_mul]
  rw [h, scanAddress_add, he]
  simp only [stride]; ring

def tickOps (r : ℕ) : List Atom :=
  [ ⟨.natOp .add 49 49 (strideReg r), trivial⟩,
    ⟨.natOp .add (stateReg r) (stateReg r) 31, trivial⟩,
    ⟨.realOp .mul (stateReg r) 12 (stateReg r), trivial⟩ ]

noncomputable def ticked (s : Store) (r : ℕ) : Store :=
  {s with
    nr := Function.update (Function.update s.nr 49 (s.nr 49 + s.nr (strideReg r)))
      (stateReg r) (s.nr (stateReg r) + 1)
    rr := Function.update s.rr (stateReg r) (s.rr 12 * s.rr (stateReg r))}

def chooseTick : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (.atom ⟨.natConst 69 n, trivial⟩)
      (.branch (.nat .eq 70 69) (.atoms (tickOps n)) (chooseTick n))

theorem tick_run (input : RAMInput) (s : Store) (r : ℕ) (hone : s.nr 31 = 1) :
    Run input (.atoms (tickOps r)) s (ticked s r) 3 := by
  have ha : stateReg r ≠ 49 := by unfold stateReg CandidateRAM.current; omega
  have hv : evalAtoms input (tickOps r) s = ticked s r := by
    simp [ticked, tickOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalReal, evalNat,
      Function.update_of_ne ha, hone]
  exact hv ▸ run_atoms input (tickOps r) s

def marked (s : Store) (r : ℕ) : Store := {s with nr := Function.update s.nr 69 r}

theorem tick_dispatch_run (input : RAMInput) (n r : ℕ) (hr : r < n) (s : Store)
    (hone : s.nr 31 = 1) (hsel : s.nr 70 = r) :
    ∃ cost, Run input (chooseTick n) s (ticked (marked s r) r) cost ∧ cost ≤ 2 * n + 4 := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    let a : Atom := ⟨.natConst 69 n, trivial⟩
    let t := marked s n
    have hm : Run input (.atom a) s t 1 := Run.atom a s
    have hone' : t.nr 31 = 1 := by simpa [t, marked] using hone
    by_cases he : r = n
    · rw [he] at hsel ⊢
      have hg : (Guard.nat .eq 70 69).eval t = true := by simp [Guard.eval, natTest, t, marked, hsel]
      exact ⟨_, Run.seq hm (Run.branchTrue hg (tick_run input t n hone')), by omega⟩
    · have hg : (Guard.nat .eq 70 69).eval t = false := by simp [Guard.eval, natTest, t, marked, hsel, he]
      obtain ⟨cost, hc, hlo⟩ := ih (by omega) t hone' (by simpa [t, marked] using hsel)
      have ht : marked t r = marked s r := by simp [t, marked, Function.update_idem]
      rw [ht] at hc
      exact ⟨_, Run.seq hm (Run.branchFalse hg hc), by omega⟩

structure Cursor {k : ℕ} (A : ClockCall k) (base v : ℕ) (S : RetrievalState A.d) (s : Store) : Prop where
  address : s.nr 49 = scanAddress base A.I.graph.n A.q v S.counts
  counts : ∀ r : Fin A.d, s.nr (stateReg r.val) = S.counts r
  coeff : ∀ r : Fin A.d, s.rr (stateReg r.val) = S.H r
  strides : ∀ r : Fin A.d, s.nr (strideReg r.val) = stride A.I.graph.n A.q r
  factor : s.rr 12 = clockZ A
  one : s.nr 31 = 1

theorem tick_cursor {k : ℕ} (A : ClockCall k) (base v : ℕ) (S : RetrievalState A.d)
    (s : Store) (r : Fin A.d) (h : Cursor A base v S s) :
    Cursor A base v (tickState A S r) (ticked (marked s r.val) r.val) := by
  have hs {x : ℕ} : 100 ≤ stateReg x := by unfold stateReg CandidateRAM.current; omega
  have ht {x : ℕ} : 100 ≤ strideReg x := by unfold strideReg CandidateRAM.current; omega
  have hst (x y : ℕ) : strideReg x ≠ stateReg y := by unfold strideReg stateReg CandidateRAM.current; omega
  have hinj {x y : ℕ} : stateReg x = stateReg y ↔ x = y := by unfold stateReg CandidateRAM.current; omega
  constructor
  · simp [ticked, marked, Function.update_of_ne (show 49 ≠ stateReg r.val by have := hs (x := r.val); omega),
      Function.update_of_ne (show strideReg r.val ≠ 69 by have := ht (x := r.val); omega),
      h.address, h.strides, tickState, scanAddress_tick]
  · intro x
    by_cases he : x = r
    · subst x
      simp [ticked, marked, tickState, h.counts, Function.update_of_ne
        (show stateReg r.val ≠ 69 by have := hs (x := r.val); omega)]
    · have hn : stateReg x.val ≠ stateReg r.val := fun e => he (Fin.ext (hinj.mp e))
      have hh := hs (x := x.val)
      simp [ticked, marked, tickState, Function.update_of_ne he, Function.update_of_ne hn,
        Function.update_of_ne (show stateReg x.val ≠ 49 by omega),
        Function.update_of_ne (show stateReg x.val ≠ 69 by omega), h.counts]
  · intro x
    by_cases he : x = r
    · subst x; simp [ticked, marked, tickState, h.coeff, h.factor]
    · have hn : stateReg x.val ≠ stateReg r.val := fun e => he (Fin.ext (hinj.mp e))
      simp [ticked, marked, tickState, Function.update_of_ne he, Function.update_of_ne hn, h.coeff]
  · intro x
    have hh := ht (x := x.val)
    simp [ticked, marked, Function.update_of_ne (hst x.val r.val),
      Function.update_of_ne (show strideReg x.val ≠ 49 by omega),
      Function.update_of_ne (show strideReg x.val ≠ 69 by omega), h.strides]
  · simp [ticked, marked, Function.update_of_ne (show 12 ≠ stateReg r.val by have := hs (x := r.val); omega),
      h.factor]
  · simp [ticked, marked, Function.update_of_ne (show 31 ≠ stateReg r.val by have := hs (x := r.val); omega),
      h.one]

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def added (dst src n : ℕ) (s : Store) : Store :=
  {s with nr := Function.update s.nr dst (s.nr dst + n * s.nr src)}

theorem add_copies_run (input : RAMInput) (dst src : ℕ) (h : src ≠ dst) (n : ℕ) (s : Store) :
    Run input (addCopies dst src n) s (added dst src n s) n := by
  induction n with
  | zero => simpa [addCopies, added] using Run.skip (input := input) s
  | succ n ih =>
    let a : Atom := ⟨.natOp .add dst dst src, trivial⟩
    have he : a.eval input (added dst src n s) = added dst src (n + 1) s := by
      simp [a, added, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, Function.update_of_ne h,
        Function.update_idem, Nat.succ_mul, Nat.add_assoc]
    exact Run.seq ih (he ▸ Run.atom a _)

def resetOps (r : ℕ) : List Atom :=
  [⟨.natConst (stateReg r) 0, trivial⟩, ⟨.realCopy (stateReg r) 13, trivial⟩]

def resetStates : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (resetStates n) (.atoms (resetOps n))

def reset (s : Store) (r : ℕ) : Store :=
  {s with nr := Function.update s.nr (stateReg r) 0, rr := Function.update s.rr (stateReg r) (s.rr 13)}

theorem state_large (r : ℕ) : 100 ≤ stateReg r := by unfold stateReg CandidateRAM.current; omega
theorem state_inj {i j : ℕ} : stateReg i = stateReg j ↔ i = j := by
  unfold stateReg CandidateRAM.current; omega
theorem stride_ne_state (r j : ℕ) : strideReg r ≠ stateReg j := by
  unfold strideReg stateReg CandidateRAM.current; omega

theorem reset_one (input : RAMInput) (r : ℕ) (s : Store) :
    Run input (.atoms (resetOps r)) s (reset s r) 2 := run_atoms input (resetOps r) s

theorem reset_states_run (input : RAMInput) (d : ℕ) (s : Store) :
    ∃ t, Run input (resetStates d) s t (2 * d) ∧
      (∀ r < d, t.nr (stateReg r) = 0 ∧ t.rr (stateReg r) = s.rr 13) ∧
      (∀ j, (∀ r < d, j ≠ stateReg r) → t.nr j = s.nr j ∧ t.rr j = s.rr j) ∧
      t.nm = s.nm ∧ t.rm = s.rm := by
  induction d with
  | zero => exact ⟨s, Run.skip s, by simp, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | succ d ih =>
    obtain ⟨p, hr, hslots, hf, hnm, hrm⟩ := ih
    have h13 : p.rr 13 = s.rr 13 := (hf 13 (fun r _ => by have := state_large r; omega)).2
    refine ⟨reset p d, ?_, ?_, ?_, hnm, hrm⟩
    · have he : 2 * d + 2 = 2 * (d + 1) := by omega
      exact he ▸ Run.seq hr (reset_one input d p)
    · intro r hrd
      by_cases he : r = d
      · subst r; simp [reset, h13]
      · have hn : stateReg r ≠ stateReg d := fun hh => he (state_inj.mp hh)
        simpa only [reset, Function.update_of_ne hn] using hslots r (by omega)
    · intro j hj
      have hne := hj d (by omega)
      simpa only [reset, Function.update_of_ne hne] using hf j (fun r hr => hj r (by omega))

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured
open TableQuery (stateReg)

def fixedNat (d : ℕ) (rs : List ℕ) (j : ℕ) : Prop :=
  j ≠ 50 ∧ j ≠ 55 ∧ j ≠ 56 ∧ (∀ r < d, j ≠ best r) ∧
    ∀ r ∈ rs, j ≠ current r ∧ j ≠ counterReg r

def fixedReal (d : ℕ) (rs : List ℕ) (j : ℕ) : Prop :=
  j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 3 ∧ (∀ r < d, j ≠ best r) ∧ ∀ r ∈ rs, j ≠ current r

structure SweepFrame (d : ℕ) (rs : List ℕ) (s t : Store) : Prop where
  natRegs : ∀ j, fixedNat d rs j → t.nr j = s.nr j
  realRegs : ∀ j, fixedReal d rs j → t.rr j = s.rr j
  natMem : t.nm = s.nm
  realMem : t.rm = s.rm

theorem SweepFrame.refl (d : ℕ) (rs : List ℕ) (s : Store) : SweepFrame d rs s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem SweepFrame.trans {d : ℕ} {rs : List ℕ} {a b c : Store} (h : SweepFrame d rs a b)
    (g : SweepFrame d rs b c) : SweepFrame d rs a c :=
  ⟨fun j hj => (g.natRegs j hj).trans (h.natRegs j hj), fun j hj => (g.realRegs j hj).trans (h.realRegs j hj),
    g.natMem.trans h.natMem, g.realMem.trans h.realMem⟩

theorem SweepFrame.cons {d : ℕ} {rs : List ℕ} {a b : Store} (h : SweepFrame d rs a b)
    (r : ℕ) : SweepFrame d (r :: rs) a b := by
  refine ⟨?_, ?_, h.natMem, h.realMem⟩
  · rintro j ⟨h₀, h₁, h₂, hb, hs⟩
    exact h.natRegs j ⟨h₀, h₁, h₂, hb, fun x hx => hs x (List.mem_cons_of_mem r hx)⟩
  · rintro j ⟨h₀, h₁, h₂, hb, hs⟩
    exact h.realRegs j ⟨h₀, h₁, h₂, hb, fun x hx => hs x (List.mem_cons_of_mem r hx)⟩

theorem fixed_small (d : ℕ) (rs : List ℕ) (j : ℕ) (hj : j < 100)
    (h₀ : j ≠ 50) (h₁ : j ≠ 55) (h₂ : j ≠ 56) : fixedNat d rs j := by
  refine ⟨h₀, h₁, h₂, fun r _ => ?_, fun r _ => ?_⟩
  · unfold best; omega
  · unfold current counterReg; dsimp [current]; omega

theorem fixed_counter (d : ℕ) (rs : List ℕ) (r : ℕ) (hr : r ∉ rs) : fixedNat d rs (counterReg r) := by
  unfold fixedNat counterReg current best
  refine ⟨by omega, by omega, by omega, fun j _ => by omega, ?_⟩
  intro j hj
  have hn : j ≠ r := fun he => hr (he ▸ hj)
  constructor <;> omega

def initializedLane (s : Store) (r : ℕ) : Store :=
  {s with nr := Function.update (Function.update s.nr (counterReg r) 0) (current r) (s.nr (stateReg r))
          rr := Function.update s.rr (current r) (s.rr (coeffReg r))}

noncomputable def advancedLane (s : Store) (r : ℕ) : Store :=
  {s with
    nr := Function.update (Function.update s.nr (counterReg r) (s.nr (counterReg r) + 1))
      (current r) (s.nr (current r) + 1)
    rr := Function.update s.rr (current r) (s.rr 12 * s.rr (current r))}

theorem lane_init_run (input : RAMInput) (s : Store) (r : ℕ) :
    Run input (.atoms (laneInit r)) s (initializedLane s r) 3 := by
  have hn : stateReg r ≠ counterReg r := by unfold stateReg counterReg; omega
  have he : evalAtoms input (laneInit r) s = initializedLane s r := by
    simp [initializedLane, laneInit, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, Function.update_of_ne hn]
  exact he ▸ run_atoms input (laneInit r) _

theorem lane_next_run (input : RAMInput) (s : Store) (r : ℕ) (h : s.nr 31 = 1) :
    Run input (.atoms (laneNext r)) s (advancedLane s r) 3 := by
  have hn : current r ≠ counterReg r := by unfold counterReg; omega
  have hs : 31 ≠ counterReg r := by unfold counterReg current; omega
  have he : evalAtoms input (laneNext r) s = advancedLane s r := by
    simp [advancedLane, laneNext, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat,
      evalReal, Function.update_of_ne hn, Function.update_of_ne hs, h]
  exact he ▸ run_atoms input (laneNext r) _

theorem lane_frames (d r : ℕ) (rs : List ℕ) (s : Store) :
    SweepFrame d (r :: rs) s (initializedLane s r) ∧ SweepFrame d (r :: rs) s (advancedLane s r) := by
  constructor
  all_goals
    refine ⟨?_, ?_, rfl, rfl⟩
    · intro j hj
      obtain ⟨hc, hn⟩ := hj.2.2.2.2 r (by simp)
      simp [initializedLane, advancedLane, Function.update_of_ne hc, Function.update_of_ne hn]
    · intro j hj
      have hc := hj.2.2.2.2 r (by simp)
      simp [initializedLane, advancedLane, Function.update_of_ne hc]

theorem lane_indices (s : Store) (r : ℕ) :
    (initializedLane s r).nr (counterReg r) = 0 ∧ (advancedLane s r).nr (counterReg r) = s.nr (counterReg r) + 1 ∧
      (initializedLane s r).nr 50 = s.nr 50 ∧ (advancedLane s r).nr 50 = s.nr 50 := by
  have hn : counterReg r ≠ current r := by unfold counterReg; omega
  have hs : 50 ≠ current r := by unfold current; omega
  have ht : 50 ≠ counterReg r := by unfold counterReg current; omega
  simp [initializedLane, advancedLane, Function.update_of_ne hn, Function.update_of_ne hs, Function.update_of_ne ht]

theorem visited_frame (d : ℕ) (s : Store) : SweepFrame d [] s (visited s d) := by
  obtain ⟨_, hn, hr, hnr, hrr⟩ := visit_frame s d
  exact ⟨fun j hj => hnr j hj.2.2.2.1 hj.1 hj.2.1 hj.2.2.1,
    fun j hj => hrr j hj.2.2.2.1 hj.1 hj.2.1 hj.2.2.1, hn, hr⟩

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured

noncomputable def foldLane (r : ℕ) (f : Store → Store) : ℕ → Store → Store
  | 0, s => s
  | n + 1, s => foldLane r f n (advancedLane (f s) r)

noncomputable def swept (d : ℕ) : List ℕ → Store → Store
  | [], s => visited s d
  | r :: rs, s => foldLane r (swept d rs) (s.nr 57) (initializedLane s r)

def sweepCost (d q : ℕ) : ℕ → ℕ
  | 0 => 5 * d + 11
  | m + 1 => 4 + q * (sweepCost d q m + 5)

theorem lane_loop_run (input : RAMInput) (d r : ℕ) (rs : List ℕ) (hr : r ∉ rs)
    (q step width limit : ℕ) (c : Cmd) (f : Store → Store)
    (hchild : ∀ s : Store, s.nr 30 = 0 → s.nr 31 = 1 → s.nr 57 = q → s.nr 59 = step →
      ∃ n, Run input c s (f s) n ∧ SweepFrame d rs s (f s) ∧ (f s).nr 50 = s.nr 50 + width ∧ n ≤ limit)
    (remaining : ℕ) (s : Store) (hz : s.nr 30 = 0) (hone : s.nr 31 = 1)
    (hq : s.nr 57 = q) (hstride : s.nr 59 = step) (hrem : s.nr (counterReg r) + remaining = q) :
    let t := foldLane r f remaining s
    ∃ n, Run input (laneLoop r c) s t n ∧ SweepFrame d (r :: rs) s t ∧
      t.nr 50 = s.nr 50 + remaining * width ∧ n ≤ 1 + remaining * (limit + 5) := by
  induction remaining generalizing s with
  | zero =>
    have he : (Guard.nat .lt (counterReg r) 57).eval s = false := by simp [Guard.eval, natTest, hq]; omega
    exact ⟨1, Run.loopFalse he, SweepFrame.refl _ _ _, by simp [foldLane], by simp⟩
  | succ m ih =>
    obtain ⟨nc, hc, hf, haddr, hcost⟩ := hchild s hz hone hq hstride
    let p := advancedLane (f s) r
    have hg : (Guard.nat .lt (counterReg r) 57).eval s = true := by simp [Guard.eval, natTest, hq]; omega
    have hfc : (f s).nr (counterReg r) = s.nr (counterReg r) := hf.natRegs _ (fixed_counter d rs r hr)
    have hfo : (f s).nr 31 = 1 := (hf.natRegs _ (fixed_small _ _ 31 (by decide) (by decide) (by decide) (by decide))).trans hone
    have hstep := lane_next_run input (f s) r hfo
    have hframe : SweepFrame d (r :: rs) s p := (hf.cons r).trans (lane_frames d r rs (f s)).2
    have hn (j : ℕ) (hj : j < 100) (ha : j ≠ 50) (hb : j ≠ 55) (hc : j ≠ 56) :=
      hframe.natRegs j (fixed_small _ _ j hj ha hb hc)
    have hindex : p.nr (counterReg r) = s.nr (counterReg r) + 1 :=
      (lane_indices (f s) r).2.1.trans (congrArg (· + 1) hfc)
    have hp : p.nr 50 = s.nr 50 + width := (lane_indices (f s) r).2.2.2.trans haddr
    obtain ⟨nt, ht, hft, hat, hct⟩ := ih p
      ((hn 30 (by decide) (by decide) (by decide) (by decide)).trans hz)
      ((hn 31 (by decide) (by decide) (by decide) (by decide)).trans hone)
      ((hn 57 (by decide) (by decide) (by decide) (by decide)).trans hq)
      ((hn 59 (by decide) (by decide) (by decide) (by decide)).trans hstride) (by omega)
    refine ⟨_, Run.loopTrue hg (Run.seq hc hstep) ht, hframe.trans hft, ?_, ?_⟩
    · change (foldLane r f m p).nr 50 = _
      rw [hat, hp, Nat.succ_mul]; omega
    · rw [Nat.succ_mul]; omega

theorem sweep_run (input : RAMInput) (d : ℕ) (rs : List ℕ) (hnd : rs.Nodup)
    (s : Store) (hz : s.nr 30 = 0) (hone : s.nr 31 = 1) :
    let t := swept d rs s
    ∃ cost, Run input (sweep d rs) s t cost ∧ SweepFrame d rs s t ∧
      t.nr 50 = s.nr 50 + s.nr 57 ^ rs.length * s.nr 59 ∧ cost ≤ sweepCost d (s.nr 57) rs.length := by
  induction rs generalizing s with
  | nil =>
    obtain ⟨cost, hrun, hc⟩ := visit_run input d s hz
    exact ⟨cost, hrun, visited_frame _ _, by simpa [swept] using (visit_frame s d).1, hc⟩
  | cons r rs ih =>
    obtain ⟨hr, htail⟩ := List.nodup_cons.mp hnd
    let p := initializedLane s r
    have hf : SweepFrame d (r :: rs) s p := (lane_frames d r rs s).1
    have hn (j : ℕ) (hj : j < 100) (ha : j ≠ 50) (hb : j ≠ 55) (hc : j ≠ 56) :=
      hf.natRegs j (fixed_small _ _ j hj ha hb hc)
    have hchild := fun (w : Store) (hwz : w.nr 30 = 0) (hwo : w.nr 31 = 1)
        (hwq : w.nr 57 = s.nr 57) (hws : w.nr 59 = s.nr 59) => by
      have h := ih htail w hwz hwo
      dsimp only at h
      rw [hwq, hws] at h
      exact h
    obtain ⟨cost, hrun, hs, ha, hc⟩ := lane_loop_run input d r rs hr (s.nr 57) (s.nr 59)
      (s.nr 57 ^ rs.length * s.nr 59) (sweepCost d (s.nr 57) rs.length)
      (sweep d rs) (swept d rs) hchild (s.nr 57) p
      ((hn 30 (by decide) (by decide) (by decide) (by decide)).trans hz)
      ((hn 31 (by decide) (by decide) (by decide) (by decide)).trans hone)
      (hn 57 (by decide) (by decide) (by decide) (by decide))
      (hn 59 (by decide) (by decide) (by decide) (by decide)) (by simp [p, (lane_indices s r).1])
    refine ⟨_, Run.seq (lane_init_run input s r) hrun, hf.trans hs, ?_, ?_⟩
    · have hp : p.nr 50 = s.nr 50 := (lane_indices s r).2.2.1
      simpa only [swept, List.length_cons, pow_succ', Nat.mul_assoc, hp] using ha
    · change 3 + cost ≤ 4 + s.nr 57 * (sweepCost d (s.nr 57) rs.length + 5)
      omega

theorem sweep_cost_bound (d q m : ℕ) :
    sweepCost d q m ≤ (5 * d + 11) * 2 ^ m * (q + 1) ^ m := by
  induction m with
  | zero => simp [sweepCost]
  | succ m ih =>
    let b := (5 * d + 11) * 2 ^ m * (q + 1) ^ m
    have h2 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
    have hq : 1 ≤ (q + 1) ^ m := Nat.one_le_pow _ _ (by omega)
    have hb : 5 ≤ b := by
      have ha := Nat.mul_le_mul (show 5 ≤ 5 * d + 11 by omega) h2
      have hh := Nat.mul_le_mul ha hq
      simpa [b] using hh
    have hi : sweepCost d q m ≤ b := ih
    have hm := Nat.mul_le_mul_left q (show sweepCost d q m + 5 ≤ 2 * b by omega)
    have he : (5 * d + 11) * 2 ^ (m + 1) * (q + 1) ^ (m + 1) = 2 * b * (q + 1) := by
      simp only [b, pow_succ]; ring
    rw [sweepCost, he]
    nlinarith

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM

def tuples {d : ℕ} (q : ℕ) : List (Fin d) → (Fin d → ℕ) → List (Fin d → ℕ)
  | [], a => [a]
  | r :: rs, a => (List.range q).flatMap (fun j => tuples q rs (Function.update a r j))

theorem update_succ {d : ℕ} (head : ℕ) (a : Fin d → ℕ) (r : Fin d) (j : ℕ) :
    Function.update (Fin.cons head a : Fin (d + 1) → ℕ) r.succ j =
      (Fin.cons head (Function.update a r j : Fin d → ℕ) : Fin (d + 1) → ℕ) := by
  funext x
  refine Fin.cases ?_ (fun x => ?_) x
  · have hn : (0 : Fin (d + 1)) ≠ r.succ := fun e => by have := congrArg Fin.val e; simp at this
    simp [Function.update_of_ne hn]
  · by_cases he : x = r
    · subst x; simp
    · have hn : x.succ ≠ r.succ := fun e => he (Fin.succ_injective _ e)
      simp [Function.update_of_ne hn, Function.update_of_ne he]

theorem tuples_succ {d : ℕ} (q head : ℕ) (rs : List (Fin d)) (a : Fin d → ℕ) :
    tuples q (rs.map Fin.succ) (Fin.cons head a) = (tuples q rs a).map (Fin.cons head) := by
  induction rs generalizing a with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, tuples, List.map_flatMap, update_succ, ih]

theorem tuples_finRange (d q : ℕ) (a : Fin d → ℕ) : tuples q (List.finRange d) a = vectors d q := by
  induction d with
  | zero =>
    have ha : a = fun r => Fin.elim0 r := Subsingleton.elim _ _
    simp [List.finRange_zero, tuples, vectors, ha]
  | succ d ih =>
    rw [List.finRange_succ, tuples, vectors]
    have hhead (j : ℕ) : Function.update a 0 j = Fin.cons j (Fin.tail a) := by
      funext x; refine Fin.cases ?_ (fun y => ?_) x
      · simp
      · simp [Fin.tail]
    simp only [hhead, tuples_succ, ih]

structure Sample (d : ℕ) where
  address : ℕ
  amounts : Fin d → ℕ
  factors : Fin d → ℝ
  objective : ℝ

structure Parameters (d : ℕ) where
  q : ℕ
  step : ℕ
  counts : Fin d → ℕ
  initial : Fin d → ℝ
  z : ℝ
  mem : ℕ → ℝ

noncomputable def sample {d : ℕ} (D : Parameters d) (addr : ℕ) (a : Fin d → ℕ) : Sample d :=
  let factors := fun r => D.z ^ a r * D.initial r
  ⟨addr, fun r => D.counts r + a r, factors, 1 - D.mem addr + ∑ r, factors r⟩

def admissible {d : ℕ} (D : Parameters d) (a : Fin d → ℕ) := ∀ r, D.counts r + a r < D.q

noncomputable def chooseSample {d : ℕ} (old : Option (Sample d)) (v : Sample d) : Option (Sample d) :=
  keepCandidate Sample.objective old v

noncomputable def sampleStep {d : ℕ} (D : Parameters d)
    (state : ℕ × Option (Sample d)) (a : Fin d → ℕ) : ℕ × Option (Sample d) := by
  classical
  exact (state.1 + D.step, if admissible D a then chooseSample state.2 (sample D state.1 a) else state.2)

noncomputable def edgeParameters {k : ℕ} (A : ClockCall k) (S : RetrievalState A.d) (u v : ℕ)
    (mem : ℕ → ℝ) : Parameters A.d :=
  ⟨A.q, (A.d + 4) * A.I.graph.n, S.counts, fun r => S.H r / clockPGF A r u v, clockZ A, mem⟩

theorem edge_sample {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (S : RetrievalState A.d)
    (u v base : ℕ) (mem : ℕ → ℝ) (a : Fin A.d → ℕ)
    (hm : mem (scanAddress base A.I.graph.n A.q u (fun r => S.counts r + a r)) =
      1 - value A T u (fun r => S.counts r + a r)) :
    let x := sample (edgeParameters A S u v mem)
      (scanAddress base A.I.graph.n A.q u (fun r => S.counts r + a r)) a
    x.objective = incrementScore A T S u v a ∧
      x.amounts = (fun r => S.counts r + a r) ∧
      x.factors = (fun r => clockZ A ^ a r * S.H r / clockPGF A r u v) := by
  dsimp only [sample, edgeParameters, incrementScore]
  rw [hm]
  simp [mul_div_assoc]

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured
open TableQuery (stateReg)

structure Loaded {d : ℕ} (D : Parameters d) (s : Store) : Prop where
  zero : s.nr 30 = 0
  one : s.nr 31 = 1
  bound : s.nr 57 = D.q
  step : s.nr 59 = D.step
  factor : s.rr 12 = D.z
  baseCounts : ∀ r : Fin d, s.nr (stateReg r.val) = D.counts r
  initial : ∀ r : Fin d, s.rr (coeffReg r.val) = D.initial r
  memory : s.rm = D.mem

def AtDigit {d : ℕ} (D : Parameters d) (r : Fin d) (j : ℕ) (s : Store) : Prop :=
  s.nr (current r.val) = D.counts r + j ∧ s.rr (current r.val) = D.z ^ j * D.initial r

def Assigned {d : ℕ} (D : Parameters d) (free : List (Fin d)) (a : Fin d → ℕ) (s : Store) : Prop :=
  ∀ r : Fin d, r ∉ free → AtDigit D r (a r) s

theorem Loaded.frame {d : ℕ} {D : Parameters d} {s t : Store} {rs : List ℕ}
    (h : Loaded D s) (hf : SweepFrame d rs s t) : Loaded D t := by
  have low (j : ℕ) (hj : j < 100) (ha : j ≠ 50) (hb : j ≠ 55) (hc : j ≠ 56) :=
    hf.natRegs j (fixed_small _ _ j hj ha hb hc)
  refine ⟨(low 30 (by decide) (by decide) (by decide) (by decide)).trans h.zero,
    (low 31 (by decide) (by decide) (by decide) (by decide)).trans h.one,
    (low 57 (by decide) (by decide) (by decide) (by decide)).trans h.bound,
    (low 59 (by decide) (by decide) (by decide) (by decide)).trans h.step, ?_, ?_, ?_, hf.realMem.trans h.memory⟩
  · apply Eq.trans (hf.realRegs 12 _) h.factor
    unfold fixedReal best current
    exact ⟨by decide, by decide, by decide, fun _ _ => by omega, fun _ _ => by omega⟩
  · intro r
    apply Eq.trans (hf.natRegs _ _) (h.baseCounts r)
    unfold fixedNat stateReg current best counterReg
    exact ⟨by omega, by omega, by omega, fun _ _ => by omega, fun _ _ => by dsimp [current]; omega⟩
  · intro r
    apply Eq.trans (hf.realRegs _ _) (h.initial r)
    unfold fixedReal coeffReg current best
    exact ⟨by omega, by omega, by omega, fun _ _ => by omega, fun _ _ => by omega⟩

theorem digit_frame {d : ℕ} {D : Parameters d} {s t : Store} {rs : List ℕ} (hf : SweepFrame d rs s t)
    {r : Fin d} (hr : r.val ∉ rs) {j : ℕ} (hv : AtDigit D r j s) : AtDigit D r j t := by
  have hn (a : ℕ) (ha : a ∈ rs) : r.val ≠ a := by intro h; exact hr (h ▸ ha)
  have hN : fixedNat d rs (current r.val) := by
    unfold fixedNat current counterReg best
    refine ⟨by omega, by omega, by omega, fun _ _ => by omega, ?_⟩
    intro a ha; have := hn a ha; dsimp [current]; omega
  have hR : fixedReal d rs (current r.val) :=
    ⟨by unfold current; omega, by unfold current; omega, by unfold current; omega, hN.2.2.2.1,
      fun a ha => (hN.2.2.2.2 a ha).1⟩
  exact ⟨(hf.natRegs _ hN).trans hv.1, (hf.realRegs _ hR).trans hv.2⟩

theorem digit_init {d : ℕ} {D : Parameters d} {s : Store} (h : Loaded D s) (r : Fin d) :
    AtDigit D r 0 (initializedLane s r.val) := by
  simp [AtDigit, initializedLane, h.baseCounts, h.initial]

theorem digit_next {d : ℕ} {D : Parameters d} {s : Store} (h : Loaded D s) (r : Fin d) (j : ℕ)
    (hv : AtDigit D r j s) : AtDigit D r (j + 1) (advancedLane s r.val) := by
  rcases hv with ⟨hn, hr⟩
  simp [AtDigit, advancedLane, hn, hr, h.factor, pow_succ, Nat.add_assoc]
  ring

noncomputable def physical (d : ℕ) (s : Store) : Sample d :=
  ⟨s.nr 50, fun r => s.nr (current r.val), fun r => s.rr (current r.val), score s d⟩

noncomputable def incumbent (d : ℕ) (s : Store) : Option (Sample d) :=
  if s.nr 56 = 0 then none else
    some ⟨s.nr 55, fun r => s.nr (best r.val), fun r => s.rr (best r.val), s.rr 3⟩

noncomputable def observe (d : ℕ) (s : Store) : ℕ × Option (Sample d) := (s.nr 50, incumbent d s)

theorem physical_sample {d : ℕ} {D : Parameters d} {s : Store} (h : Loaded D s)
    (a : Fin d → ℕ) (ha : ∀ r, AtDigit D r (a r) s) :
    physical d s = sample D (s.nr 50) a := by
  have hn (r : Fin d) := (ha r).1
  have hf (r : Fin d) := (ha r).2
  simp only [physical, sample, score, ← Fin.sum_univ_eq_sum_range (fun r => s.rr (current r)), h.memory, hn, hf]

theorem incumbent_saved (s : Store) (d : ℕ) : incumbent d (saved (scored s d) d) = some (physical d s) := by
  obtain ⟨hp, hflag, hscore, hl⟩ := saved_fields d s
  simp only [incumbent, hflag, Nat.one_ne_zero, if_false, hp, hscore, physical]
  congr 2
  · funext r; exact (hl r.val r.isLt).1
  · funext r; exact (hl r.val r.isLt).2

theorem incumbent_scored (s : Store) (d : ℕ) : incumbent d (scored s d) = incumbent d s := by
  have h0 (r : Fin d) : best r.val ≠ 0 := by unfold best; omega
  have h1 (r : Fin d) : best r.val ≠ 1 := by unfold best; omega
  simp [incumbent, scored, Function.update_of_ne (h0 _), Function.update_of_ne (h1 _)]

theorem incumbent_considered (s : Store) (d : ℕ) :
    incumbent d (considered s d) = chooseSample (incumbent d s) (physical d s) := by
  unfold considered chooseSample
  by_cases h : s.nr 56 = 0
  · rw [if_pos (Or.inl h), incumbent_saved]
    simp [h, incumbent, keepCandidate]
  · by_cases hs : score s d < s.rr 3
    · rw [if_pos (Or.inr hs), incumbent_saved]
      simp [incumbent, h, keepCandidate, physical, hs]
    · rw [if_neg (not_or.mpr ⟨h, hs⟩), incumbent_scored]
      simp [incumbent, h, keepCandidate, physical, hs]

theorem incumbent_advanced (s : Store) (d : ℕ) : incumbent d (advanced s) = incumbent d s := by
  have hn (r : Fin d) : best r.val ≠ 50 := by unfold best; omega
  simp [incumbent, advanced, Function.update_of_ne (hn _)]

theorem visit_observe {d : ℕ} {D : Parameters d} {s : Store} (h : Loaded D s) (a : Fin d → ℕ)
    (ha : ∀ r, AtDigit D r (a r) s) : observe d (visited s d) = sampleStep D (observe d s) a := by
  classical
  have hv : within d s ↔ admissible D a := by
    constructor
    · intro hw r
      have hx := hw r.val r.isLt
      rwa [(ha r).1, h.bound] at hx
    · intro hw j hj
      rw [show s.nr (current j) = _ from (ha ⟨j, hj⟩).1, h.bound]; exact hw ⟨j, hj⟩
  apply Prod.ext
  · exact (visit_frame s d).1.trans (congrArg (s.nr 50 + ·) h.step)
  · change incumbent d (visited s d) = _
    by_cases hh : admissible D a
    · simp only [visited, if_pos (hv.mpr hh), incumbent_advanced, incumbent_considered, physical_sample h a ha,
        sampleStep, observe, if_pos hh]
    · simp only [visited, if_neg (fun hx => hh (hv.mp hx)), incumbent_advanced, sampleStep, observe, if_neg hh]

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM

theorem scan_address_at {d : ℕ} (base n q v : ℕ) (i : Fin d → ℕ) (j : ℕ) (hj : j < (vectors d q).length) :
    scanAddress base n q v (fun r => i r + (vectors d q)[j] r) =
      scanAddress base n q v i + j * ((d + 4) * n) := by
  have hh := congrArg (fun xs : List ℕ => xs[j]?) (scanAddress_order base n q v i)
  have hr : j < (List.range (q ^ d)).length := by simpa [length_vectors] using hj
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hr,
    Option.map_some, List.getElem_range, Option.some.injEq] using hh

theorem fold_addresses {d : ℕ} (D : Parameters d) (xs : List (Fin d → ℕ)) (addr : (Fin d → ℕ) → ℕ)
    (base : ℕ) (old : Option (Sample d))
    (indexed : ∀ j (hj : j < xs.length), addr xs[j] = base + j * D.step) :
    (xs.foldl (sampleStep D) (base, old)).2 =
      xs.foldl (fun b a => if ∀ r, D.counts r + a r < D.q then chooseSample b (sample D (addr a) a) else b) old := by
  classical
  induction xs generalizing base old with
  | nil => rfl
  | cons a xs ih =>
    have h0 := indexed 0 (by simp)
    change addr a = base + 0 * D.step at h0
    simp only [Nat.zero_mul, Nat.add_zero] at h0
    have htail (j : ℕ) (hj : j < xs.length) : addr xs[j] = base + D.step + j * D.step := by
      have hh := indexed (j + 1) (by simp; omega)
      simpa only [List.getElem_cons_succ, Nat.succ_mul, Nat.add_assoc, Nat.add_comm D.step] using hh
    by_cases hv : ∀ r, D.counts r + a r < D.q
    · have hh : admissible D a := hv
      simpa only [List.foldl_cons, sampleStep, h0, if_pos hh, if_pos hv] using
        ih (base + D.step) (chooseSample old (sample D base a)) htail
    · have hh : ¬admissible D a := hv
      simpa only [List.foldl_cons, sampleStep, h0, if_neg hh, if_neg hv] using
        ih (base + D.step) old htail

theorem fold_choice_image {α β : Type} (f : α → ℝ) (g : α → β) (score : β → ℝ)
    (valid : α → Prop) [DecidablePred valid] (agree : ∀ x, valid x → score (g x) = f x)
    (xs : List α) (old : Option α) (hprev : ∀ w, old = some w → valid w) :
    xs.foldl (fun b a => if valid a then keepCandidate score b (g a) else b) (old.map g) =
      (xs.foldl (fun b a => if valid a then keepCandidate f b a else b) old).map g := by
  induction xs generalizing old with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons]
    by_cases ha : valid a
    · simp only [if_pos ha]
      cases old with
      | none =>
        simp only [Option.map_none, keepCandidate]
        exact ih (some a) (fun w hw => Option.some.inj hw ▸ ha)
      | some b =>
        have hb := hprev b rfl
        by_cases hlt : f a < f b
        · simp only [Option.map_some, keepCandidate, agree a ha, agree b hb, if_pos hlt]
          exact ih (some a) (fun w hw => Option.some.inj hw ▸ ha)
        · simp only [Option.map_some, keepCandidate, agree a ha, agree b hb, if_neg hlt]
          exact ih (some b) (fun w hw => Option.some.inj hw ▸ hb)
    · simp only [if_neg ha]
      exact ih old hprev

theorem edge_scan_minimum {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (S : RetrievalState A.d)
    (u v base : ℕ) (mem : ℕ → ℝ) (a : Fin A.d → ℕ) (rest : List (Fin A.d → ℕ))
    (hr : rectangle A S.counts = a :: rest)
    (hm : ∀ i : Fin A.d → ℕ, (∀ r, i r < A.q) →
      mem (scanAddress base A.I.graph.n A.q u i) = 1 - (T u i).value) :
    let D := edgeParameters A S u v mem
    let b := selectMin (incrementScore A T S u v) (a :: rest) a
    let addr := fun x : Fin A.d → ℕ => scanAddress base A.I.graph.n A.q u (fun r => S.counts r + x r)
    ((vectors A.d A.q).foldl (sampleStep D) (scanAddress base A.I.graph.n A.q u S.counts, none)).2 =
      some (sample D (addr b) b) := by
  classical
  dsimp only
  let D := edgeParameters A S u v mem
  let addr := fun x : Fin A.d → ℕ => scanAddress base A.I.graph.n A.q u (fun r => S.counts r + x r)
  let g := fun x => sample D (addr x) x
  let f := incrementScore A T S u v
  let valid := fun x : Fin A.d → ℕ => ∀ r, S.counts r + x r < A.q
  have hagree (x : Fin A.d → ℕ) (hx : valid x) : (g x).objective = f x := by
    have hval := hm (fun r => S.counts r + x r) hx
    rw [← value_of_valid A T u _ hx] at hval
    exact (edge_sample A T S u v base mem x hval).1
  have h1 := fold_addresses D (vectors A.d A.q) addr (scanAddress base A.I.graph.n A.q u S.counts) none
    (fun j hj => scan_address_at base A.I.graph.n A.q u S.counts j hj)
  have h2 := fold_choice_image f g Sample.objective valid hagree (vectors A.d A.q) none (by simp)
  have h3 := rectangle_scan_choice A S.counts f a rest hr
  exact h1.trans (h2.trans (congrArg (Option.map g) h3))

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured

theorem lane_observe (d : ℕ) (s : Store) (r : ℕ) :
    observe d (initializedLane s r) = observe d s ∧ observe d (advancedLane s r) = observe d s := by
  have hc (j : ℕ) (hj : j < 100) : j ≠ current r := by unfold current; omega
  have hn (j : ℕ) (hj : j < 100) : j ≠ counterReg r := by unfold counterReg current; omega
  have hb (x : ℕ) : best x ≠ current r := by unfold current best; omega
  have ht (x : ℕ) : best x ≠ counterReg r := by unfold counterReg current best; omega
  simp [observe, incumbent, initializedLane, advancedLane, Function.update_of_ne (hc 50 (by decide)),
    Function.update_of_ne (hc 55 (by decide)), Function.update_of_ne (hc 56 (by decide)),
    Function.update_of_ne (hc 3 (by decide)), Function.update_of_ne (hn 50 (by decide)),
    Function.update_of_ne (hn 55 (by decide)), Function.update_of_ne (hn 56 (by decide)),
    Function.update_of_ne (hb _), Function.update_of_ne (ht _)]

theorem val_not_mem {d : ℕ} {r : Fin d} {rs : List (Fin d)} (h : r ∉ rs) :
    r.val ∉ rs.map Fin.val := by
  rintro hs
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hs
  exact h (Fin.ext he ▸ ha)

theorem assigned_frame {d : ℕ} {D : Parameters d} {s t : Store} {a : Fin d → ℕ}
    {rs : List (Fin d)} (hf : SweepFrame d (rs.map Fin.val) s t) (h : Assigned D rs a s) : Assigned D rs a t :=
  fun r hr => digit_frame hf (val_not_mem hr) (h r hr)

theorem fold_lane_observe {d : ℕ} (D : Parameters d) (input : RAMInput) (r : Fin d) (rs : List (Fin d))
    (hr : r ∉ rs) (hnd : rs.Nodup)
    (child : ∀ (s : Store) (a : Fin d → ℕ), Loaded D s → Assigned D rs a s →
      observe d (swept d (rs.map Fin.val) s) = (tuples D.q rs a).foldl (sampleStep D) (observe d s))
    (remaining j : ℕ) (s : Store) (a : Fin d → ℕ) (hl : Loaded D s)
    (hp : Assigned D (r :: rs) a s) (hj : AtDigit D r j s) :
    observe d (foldLane r.val (swept d (rs.map Fin.val)) remaining s) =
      (List.range' j remaining).foldl (fun b n => (tuples D.q rs (Function.update a r n)).foldl (sampleStep D) b)
        (observe d s) := by
  induction remaining generalizing s j with
  | zero => rfl
  | succ m ih =>
    have hinner : Assigned D rs (Function.update a r j) s := by
      intro v hv
      by_cases he : v = r
      · subst v; simpa using hj
      · simpa [Function.update_of_ne he] using hp v (by simp [he, hv])
    let w := swept d (rs.map Fin.val) s
    obtain ⟨_, _, hf, _, _⟩ := sweep_run input d (rs.map Fin.val)
      (hnd.map Fin.val_injective) s hl.zero hl.one
    have hw : Loaded D w := hl.frame hf
    have htrace : observe d w = _ := child s (Function.update a r j) hl hinner
    let p := advancedLane w r.val
    have hshift : SweepFrame d ((r :: rs).map Fin.val) s p :=
      (hf.cons r.val).trans (lane_frames d r.val (rs.map Fin.val) w).2
    have hnext : AtDigit D r (j + 1) p := digit_next hw r j (digit_frame hf (val_not_mem hr) hj)
    have he := ih (j + 1) p (hl.frame hshift) (assigned_frame hshift hp) hnext
    have ho : observe d p = observe d w := (lane_observe d w r.val).2
    simpa only [foldLane, List.range'_succ, List.foldl_cons, ho, htrace] using he

theorem sweep_observe {d : ℕ} (D : Parameters d) (input : RAMInput) (rs : List (Fin d))
    (hnd : rs.Nodup) (s : Store) (a : Fin d → ℕ) (hl : Loaded D s) (ha : Assigned D rs a s) :
    observe d (swept d (rs.map Fin.val) s) = (tuples D.q rs a).foldl (sampleStep D) (observe d s) := by
  induction rs generalizing s a with
  | nil =>
    exact visit_observe hl a (fun r => ha r (by simp))
  | cons r rs ih =>
    obtain ⟨hr, htail⟩ := List.nodup_cons.mp hnd
    let p := initializedLane s r.val
    have hf : SweepFrame d ((r :: rs).map Fin.val) s p := (lane_frames d r.val (rs.map Fin.val) s).1
    have h := fold_lane_observe D input r rs hr htail (ih htail) D.q 0 p a
      (hl.frame hf) (assigned_frame hf ha) (digit_init hl r)
    have ho : observe d p = observe d s := (lane_observe d s r.val).1
    simpa only [swept, List.map_cons, hl.bound, tuples, List.foldl_flatMap,
      List.range_eq_range', ho] using h

theorem edge_sweep {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (S : RetrievalState A.d)
    (u v base : ℕ) (mem : ℕ → ℝ) (a : Fin A.d → ℕ) (rest : List (Fin A.d → ℕ))
    (hr : rectangle A S.counts = a :: rest)
    (hm : ∀ i : Fin A.d → ℕ, (∀ r, i r < A.q) →
      mem (scanAddress base A.I.graph.n A.q u i) = 1 - (T u i).value)
    (input : RAMInput) (s : Store) (hl : Loaded (edgeParameters A S u v mem) s)
    (haddress : s.nr 50 = scanAddress base A.I.graph.n A.q u S.counts) (hempty : s.nr 56 = 0) :
    let b := selectMin (incrementScore A T S u v) (a :: rest) a
    let addr := scanAddress base A.I.graph.n A.q u (fun r => S.counts r + b r)
    ∃ out steps, Run input (sweep A.d ((List.finRange A.d).map Fin.val)) s out steps ∧
      incumbent A.d out = some (sample (edgeParameters A S u v mem) addr b) ∧
      SweepFrame A.d ((List.finRange A.d).map Fin.val) s out ∧
      steps ≤ (5 * A.d + 11) * 2 ^ A.d * (A.q + 1) ^ A.d := by
  let D := edgeParameters A S u v mem
  let rs := List.finRange A.d
  have hnd : rs.Nodup := List.nodup_finRange _
  obtain ⟨n, hrun, hf, _, hc⟩ := sweep_run input A.d (rs.map Fin.val) (hnd.map Fin.val_injective) s hl.zero hl.one
  let out := swept A.d (rs.map Fin.val) s
  have hs := sweep_observe D input rs hnd s (fun _ => 0) hl (fun r h => False.elim (h (List.mem_finRange r)))
  have hobs : observe A.d s = (scanAddress base A.I.graph.n A.q u S.counts, none) := by
    simp [observe, incumbent, hempty, haddress]
  rw [hobs] at hs
  have hmin := edge_scan_minimum A T S u v base mem a rest hr hm
  have hs' := congrArg Prod.snd hs
  simp only [rs, tuples_finRange] at hs'
  refine ⟨out, n, hrun, hs'.trans hmin, hf, ?_⟩
  have hq : s.nr 57 = A.q := hl.bound
  simpa only [rs, List.length_map, List.length_finRange, hq] using
    hc.trans (sweep_cost_bound A.d (s.nr 57) (rs.map Fin.val).length)

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def partialProduct (s : Store) (j : ℕ) : Store :=
  {s with nr := Function.update (Function.update s.nr 62 (j * s.nr 58)) 61 j}

theorem product_step (input : RAMInput) (s : Store) (j : ℕ) (hone : s.nr 31 = 1) :
    Run input (.atoms productBody) (partialProduct s j) (partialProduct s (j + 1)) 2 := by
  have he : evalAtoms input productBody (partialProduct s j) = partialProduct s (j + 1) := by
    apply Store.ext
    · funext r
      by_cases h61 : r = 61 <;> by_cases h62 : r = 62 <;>
        simp [productBody, partialProduct, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
          evalNat, h61, h62, hone, Nat.succ_mul]
    · rfl
    · rfl
    · rfl
  exact he ▸ run_atoms input productBody (partialProduct s j)

theorem product_loop_run (input : RAMInput) (s : Store) (hone : s.nr 31 = 1)
    (remaining j : ℕ) (hend : j + remaining = s.nr 57) :
    Run input productLoop (partialProduct s j) (partialProduct s (s.nr 57)) (4 * remaining + 1) := by
  induction remaining generalizing j with
  | zero =>
    have he : j = s.nr 57 := by omega
    subst j
    exact Run.loopFalse (by simp [Guard.eval, natTest, partialProduct])
  | succ n ih =>
    have hg : (Guard.nat .lt 61 57).eval (partialProduct s j) = true := by
      simp [Guard.eval, natTest, partialProduct, show j < s.nr 57 by omega]
    have ht := ih (j + 1) (by omega)
    have hx := Run.loopTrue hg (product_step input s j hone) ht
    simpa only [productLoop, show 1 + 2 + 1 + (4 * n + 1) = 4 * (n + 1) + 1 by omega] using hx

def productResult (s : Store) : Store :=
  let p := partialProduct s (s.nr 57)
  {p with nr := Function.update p.nr 58 (s.nr 57 * s.nr 58)}

theorem product_run (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) :
    Run input productCmd s (productResult s) (4 * s.nr 57 + 4) := by
  have h0 : evalAtoms input productInit s = partialProduct s 0 := by
    simp [evalAtoms, productInit, Atom.eval, Store.ofRAM, ramStep, Store.at, partialProduct]
  have hf : productLast.eval input (partialProduct s (s.nr 57)) = productResult s := by
    simp [productResult, partialProduct, productLast, Atom.eval, Store.ofRAM, ramStep, Store.at]
  have he := Run.seq (h0 ▸ run_atoms input productInit s)
    (Run.seq (product_loop_run input s hone (s.nr 57) 0 (by omega)) (hf ▸ Run.atom productLast _))
  simpa only [productInit, List.length_cons, List.length_nil, productCmd,
    show 2 + (4 * s.nr 57 + 1 + 1) = 4 * s.nr 57 + 4 by omega] using he

def recorded (s : Store) (r : ℕ) : Store := {s with nr := Function.update s.nr (strideReg r) (s.nr 58)}

theorem stride_large (r : ℕ) : 100 ≤ strideReg r := by unfold strideReg CandidateRAM.current; omega
theorem stride_inj {i j : ℕ} : strideReg i = strideReg j ↔ i = j := by
  unfold strideReg CandidateRAM.current; omega

theorem record_run (input : RAMInput) (s : Store) (r : ℕ) (hone : s.nr 31 = 1) :
    let t := productResult (recorded s r)
    Run input (recordCmd r) s t (4 * s.nr 57 + 5) ∧ t.nr 58 = s.nr 57 * s.nr 58 ∧
      t.nr (strideReg r) = s.nr 58 ∧
      (∀ j, j ≠ strideReg r → j ≠ 58 → j ≠ 61 → j ≠ 62 → t.nr j = s.nr j) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  let p := recorded s r
  have hh := stride_large r
  have h31 : 31 ≠ strideReg r := by omega
  have h57 : 57 ≠ strideReg r := by omega
  have h58 : 58 ≠ strideReg r := by omega
  have hp : Run input (.atom (recordStride r)) s p 1 := Run.atom _ _
  have ht := product_run input p (by simpa [p, recorded, Function.update_of_ne h31] using hone)
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · have he : 1 + (4 * p.nr 57 + 4) = 4 * s.nr 57 + 5 := by
      simp [p, recorded, Function.update_of_ne h57]; omega
    exact he ▸ Run.seq hp ht
  · simp [productResult, recorded, Function.update_of_ne h57, Function.update_of_ne h58]
  · simp [productResult, recorded, partialProduct, Function.update_of_ne h58.symm,
      Function.update_of_ne (show strideReg r ≠ 61 by omega),
      Function.update_of_ne (show strideReg r ≠ 62 by omega)]
  · intro j hs h₈ h₁ h₂
    simp [productResult, recorded, partialProduct, Function.update_of_ne hs,
      Function.update_of_ne h₈, Function.update_of_ne h₁, Function.update_of_ne h₂]

theorem powers_run (input : RAMInput) (s : Store) (d : ℕ) (hone : s.nr 31 = 1) :
    ∃ t, Run input (powers d) s t (d * (4 * s.nr 57 + 5)) ∧
      t.nr 58 = s.nr 58 * s.nr 57 ^ d ∧
      (∀ r < d, t.nr (strideReg r) = s.nr 58 * s.nr 57 ^ (d - 1 - r)) ∧
      (∀ j, (∀ r < d, j ≠ strideReg r) → j ≠ 58 → j ≠ 61 → j ≠ 62 → t.nr j = s.nr j) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  induction d generalizing s with
  | zero =>
    refine ⟨s, by simpa [powers] using Run.skip (input := input) s, by simp,
      by simp, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ d ih =>
    let p := productResult (recorded s d)
    obtain ⟨hrun, hp, hs, hf, hrr, hnm, hrm⟩ := record_run input s d hone
    have hg := stride_large d
    have h31 : p.nr 31 = s.nr 31 := hf 31 (by omega) (by decide) (by decide) (by decide)
    have h57 : p.nr 57 = s.nr 57 := hf 57 (by omega) (by decide) (by decide) (by decide)
    obtain ⟨t, ht, htval, hslots, hrest, tr, tn, tm⟩ := ih p (h31.trans hone)
    rw [h57] at ht htval hslots
    have hpc : p.nr 58 = s.nr 57 * s.nr 58 := hp
    rw [hpc] at htval hslots
    refine ⟨t, ?_, ?_, ?_, ?_, tr.trans hrr, tn.trans hnm, tm.trans hrm⟩
    · have hc : 4 * s.nr 57 + 5 + d * (4 * s.nr 57 + 5) = (d + 1) * (4 * s.nr 57 + 5) := by ring
      exact hc ▸ Run.seq hrun ht
    · rw [htval, pow_succ]; ring
    · intro r hr
      by_cases he : r = d
      · subst r
        have hh := hrest (strideReg d) (fun j hj h => by have := stride_inj.mp h; omega)
          (by omega) (by omega) (by omega)
        simpa using hh.trans hs
      · have hj : r < d := by omega
        have hn : d + 1 - 1 - r = (d - 1 - r) + 1 := by omega
        rw [hn, pow_succ, hslots r hj]
        ring
    · intro j hne h₈ h₁ h₂
      exact (hrest j (fun r hr => hne r (by omega)) h₈ h₁ h₂).trans
        (hf j (hne d (by omega)) h₈ h₁ h₂)

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def readOps (k : ℕ) : List Atom :=
  [ ⟨.natConst 31 1, trivial⟩, ⟨.natConst 30 0, trivial⟩, ⟨.natConst 61 2, trivial⟩,
    ⟨.loadNat 60 61, trivial⟩, ⟨.loadNat 57 30, trivial⟩, ⟨.natConst 59 0, trivial⟩,
    ⟨.natConst 64 (33 + 2 * k), trivial⟩, ⟨.natOp .add 61 0 0, trivial⟩,
    ⟨.natOp .add 61 61 61, trivial⟩, ⟨.natOp .add 61 64 61, trivial⟩,
    ⟨.loadNat 49 61, trivial⟩, ⟨.natConst 61 4, trivial⟩, ⟨.natOp .add 49 49 61, trivial⟩,
    ⟨.loadReal 12 30, trivial⟩, ⟨.loadReal 13 31, trivial⟩ ]

def copyWidth : Atom := ⟨.natCopy 58 59, trivial⟩
def seedCmd (k d : ℕ) : Cmd :=
  .seq (.atoms (readOps k)) (.seq (addCopies 59 60 (d + 4)) (.seq (addCopies 49 0 (d + 4)) (.atom copyWidth)))
def startTable (k d : ℕ) : Cmd := .seq (seedCmd k d) (.seq (powers d) (resetStates d))

noncomputable def seeded (k d : ℕ) (input : RAMInput) (s : Store) : Store :=
  copyWidth.eval input (added 49 0 (d + 4) (added 59 60 (d + 4) (evalAtoms input (readOps k) s)))

theorem seed_run (k d : ℕ) (input : RAMInput) (s : Store) :
    Run input (seedCmd k d) s (seeded k d input s) (2 * d + 24) := by
  have hs := run_atoms input (readOps k) s
  have h1 := add_copies_run input 59 60 (by decide) (d + 4) (evalAtoms input (readOps k) s)
  have h2 := add_copies_run input 49 0 (by decide) (d + 4)
    (added 59 60 (d + 4) (evalAtoms input (readOps k) s))
  have h := Run.seq hs (Run.seq h1 (Run.seq h2 (Run.atom copyWidth _)))
  have hn : (readOps k).length + (d + 4 + (d + 4 + 1)) = 2 * d + 24 := by
    change 15 + (d + 4 + (d + 4 + 1)) = _; omega
  exact hn ▸ h

structure Seeds (k d : ℕ) (s w : Store) : Prop where
  front : w.nr 0 = s.nr 0
  zero : w.nr 30 = 0
  one : w.nr 31 = 1
  q : w.nr 57 = s.nm 0
  width : w.nr 59 = (d + 4) * s.nm 2
  power : w.nr 58 = (d + 4) * s.nm 2
  address : w.nr 49 = s.nm (targetSlot k (s.nr 0) + 1) + 4 + (d + 4) * s.nr 0
  factor : w.rr 12 = s.rm 0
  initial : w.rr 13 = s.rm 1
  natMem : w.nm = s.nm
  realMem : w.rm = s.rm

theorem seed_fields (k d : ℕ) (input : RAMInput) (s : Store) : Seeds k d s (seeded k d input s) := by
  have ha : 33 + 2 * k + (s.nr 0 + s.nr 0 + (s.nr 0 + s.nr 0)) = targetSlot k (s.nr 0) + 1 := by
    unfold targetSlot; omega
  constructor <;>
    simp [seeded, copyWidth, added, readOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, ha]

theorem start_run {k : ℕ} (A : ClockCall k) (base t : ℕ) (input : RAMInput) (s : Store)
    (ht : s.nr 0 = t) (hc : s.nm (targetSlot k t + 1) = base)
    (hn : s.nm 2 = A.I.graph.n) (hq : s.nm 0 = A.q)
    (hz : s.rm 0 = clockZ A) (hh : s.rm 1 = 1 / (8 * (k : ℝ))) :
    ∃ out, Run input (startTable k A.d) s out (2 * A.d + 24 + (A.d * (4 * A.q + 5) + 2 * A.d)) ∧
      Cursor A base t ⟨[t], fun _ => 0, fun _ => 1 / (8 * (k : ℝ))⟩ out ∧
      out.nr 57 = A.q ∧ out.nr 59 = (A.d + 4) * A.I.graph.n ∧
      out.nr 58 = (A.d + 4) * A.I.graph.n * A.q ^ A.d ∧
      out.nr 0 = t ∧ out.nr 30 = 0 ∧ out.nm = s.nm ∧ out.rm = s.rm := by
  let p := seeded k A.d input s
  have hp := seed_fields k A.d input s
  obtain ⟨w, hwrun, hpow, hs, hf, wr, wn, wm⟩ := powers_run input p A.d hp.one
  obtain ⟨out, horun, hcoords, hsame, onm, orm⟩ := reset_states_run input A.d w
  have hwsmall (r : ℕ) (hrs : r < 100) (h₀ : r ≠ 58) (h₁ : r ≠ 61) (h₂ : r ≠ 62) :
      w.nr r = p.nr r := hf r (fun j _ => by have := stride_large j; omega) h₀ h₁ h₂
  have hsmall (r : ℕ) (hr : r < 100) : out.nr r = w.nr r ∧ out.rr r = w.rr r :=
    hsame r (fun j _ => by have := state_large j; omega)
  have hq' : p.nr 57 = A.q := hp.q.trans hq
  have hw' : p.nr 58 = (A.d + 4) * A.I.graph.n := hp.power.trans (by rw [hn])
  rw [hq'] at hwrun
  refine ⟨out, Run.seq (seed_run k A.d input s) (Run.seq hwrun horun), ?_,
    (hsmall 57 (by decide)).1.trans ((hwsmall 57 (by decide) (by decide) (by decide) (by decide)).trans hq'),
    ?_, ?_, ?_, ?_, onm.trans (wn.trans hp.natMem), orm.trans (wm.trans hp.realMem)⟩
  · constructor
    · have h49 := (hsmall 49 (by decide)).1.trans
        ((hwsmall 49 (by decide) (by decide) (by decide) (by decide)).trans hp.address)
      simpa [ht, hc, scanAddress, vectorIndex] using h49
    · intro r; exact (hcoords r.val r.isLt).1
    · intro r
      exact (hcoords r.val r.isLt).2.trans ((congrFun wr 13).trans (hp.initial.trans hh))
    · intro r
      have hkeep := (hsame (strideReg r.val) (fun j _ => stride_ne_state r.val j)).1
      simpa only [stride, hw', hq'] using hkeep.trans (hs r.val r.isLt)
    · exact (hsmall 12 (by decide)).2.trans ((congrFun wr 12).trans (hp.factor.trans hz))
    · exact (hsmall 31 (by decide)).1.trans ((hwsmall 31 (by decide) (by decide) (by decide) (by decide)).trans hp.one)
  · exact (hsmall 59 (by decide)).1.trans
      ((hwsmall 59 (by decide) (by decide) (by decide) (by decide)).trans (hp.width.trans (by rw [hn])))
  · simpa only [hw', hq'] using (hsmall 58 (by decide)).1.trans hpow
  · exact (hsmall 0 (by decide)).1.trans ((hwsmall 0 (by decide) (by decide) (by decide) (by decide)).trans (hp.front.trans ht))
  · exact (hsmall 30 (by decide)).1.trans ((hwsmall 30 (by decide) (by decide) (by decide) (by decide)).trans hp.zero)

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured
open CandidateRAM (coeffReg Loaded edgeParameters)

def positionOps : List Atom :=
  [⟨.natCopy 50 49, trivial⟩, ⟨.natConst 60 0, trivial⟩, ⟨.natConst 56 0, trivial⟩]
def subtractVertex : Atom := ⟨.natOp .sub 50 50 60, trivial⟩
def positionCmd (d : ℕ) : Cmd :=
  .seq (.atoms positionOps) (.seq (addCopies 60 0 (d + 4))
    (.seq (.atom subtractVertex) (addCopies 50 70 (d + 4))))

noncomputable def positioned (d : ℕ) (input : RAMInput) (s : Store) : Store :=
  added 50 70 (d + 4) (subtractVertex.eval input (added 60 0 (d + 4) (evalAtoms input positionOps s)))

theorem position_run (d : ℕ) (input : RAMInput) (s : Store) :
    Run input (positionCmd d) s (positioned d input s) (2 * d + 12) := by
  let a := evalAtoms input positionOps s
  let b := added 60 0 (d + 4) a
  let c := subtractVertex.eval input b
  have he := Run.seq (run_atoms input positionOps s)
    (Run.seq (add_copies_run input 60 0 (by decide) (d + 4) a)
      (Run.seq (Run.atom subtractVertex b) (add_copies_run input 50 70 (by decide) (d + 4) c)))
  have hn : positionOps.length + (d + 4 + (1 + (d + 4))) = 2 * d + 12 := by
    change 3 + (d + 4 + (1 + (d + 4))) = _; omega
  exact hn ▸ he

theorem position_fields (d : ℕ) (input : RAMInput) (s : Store) :
    let t := positioned d input s
    t.nr 50 = (s.nr 49 - (d + 4) * s.nr 0) + (d + 4) * s.nr 70 ∧ t.nr 56 = 0 ∧
      (∀ j, j ≠ 50 → j ≠ 56 → j ≠ 60 → t.nr j = s.nr j) ∧ t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  simp +contextual [positioned, positionOps, added, subtractVertex, evalAtoms, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat]

def divideOps (r : ℕ) : List Atom :=
  [ ⟨.natConst 67 (4 + r), trivial⟩, ⟨.natOp .add 67 49 67, trivial⟩, ⟨.loadReal 6 67, trivial⟩,
    ⟨.realOp .div (coeffReg r) (stateReg r) 6, trivial⟩ ]
def divideCoeffs : ℕ → Cmd
  | 0 => .skip
  | d + 1 => .seq (divideCoeffs d) (.atoms (divideOps d))

theorem divide_one (r : ℕ) (input : RAMInput) (s : Store) :
    let t := evalAtoms input (divideOps r) s
    t.rr (coeffReg r) = s.rr (stateReg r) / s.rm (s.nr 49 + 4 + r) ∧
      (∀ j, j ≠ 67 → t.nr j = s.nr j) ∧ (∀ j, j ≠ 6 → j ≠ coeffReg r → t.rr j = s.rr j) ∧
      t.nm = s.nm ∧ t.rm = s.rm := by
  have hh : stateReg r ≠ 6 := by have := state_large r; omega
  simp +contextual [divideOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, evalReal,
    hh, Nat.add_assoc]

theorem divide_run (input : RAMInput) (d : ℕ) (s : Store) :
    ∃ out, Run input (divideCoeffs d) s out (4 * d) ∧
      (∀ r < d, out.rr (coeffReg r) = s.rr (stateReg r) / s.rm (s.nr 49 + 4 + r)) ∧
      (∀ j, j ≠ 67 → out.nr j = s.nr j) ∧
      (∀ j, j ≠ 6 → (∀ r < d, j ≠ coeffReg r) → out.rr j = s.rr j) ∧ out.nm = s.nm ∧ out.rm = s.rm := by
  induction d with
  | zero => exact ⟨s, Run.skip s, by simp, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩
  | succ d ih =>
    obtain ⟨p, hp, hc, hnr, hrr, hnm, hrm⟩ := ih
    let t := evalAtoms input (divideOps d) p
    obtain ⟨ht, tn, tr, tnm, trm⟩ := divide_one d input p
    have hold : p.rr (stateReg d) = s.rr (stateReg d) :=
      hrr _ (by have := state_large d; omega) (fun r _ => by unfold stateReg coeffReg CandidateRAM.current; omega)
    have hcost : 4 * d + (divideOps d).length = 4 * (d + 1) := by simp [divideOps]; omega
    refine ⟨t, hcost ▸ Run.seq hp (run_atoms input _ _), ?_, fun j hj => (tn j hj).trans (hnr j hj),
      ?_, tnm.trans hnm, trm.trans hrm⟩
    · intro r hr
      by_cases he : r = d
      · subst r
        rw [hold, hrm, hnr 49 (by decide)] at ht
        exact ht
      · have hn : coeffReg r ≠ coeffReg d := by unfold coeffReg CandidateRAM.current; omega
        exact (tr _ (by unfold coeffReg CandidateRAM.current; omega) hn).trans (hc r (by omega))
    · intro j hj hs
      exact (tr j hj (hs d (by omega))).trans (hrr j hj (fun r hr => hs r (by omega)))

def prepareEdge (d : ℕ) : Cmd := .seq (positionCmd d) (divideCoeffs d)

theorem prepare_edge_run {k : ℕ} (A : ClockCall k) (S : RetrievalState A.d) (u v base : ℕ)
    (input : RAMInput) (s : Store) (hcur : Cursor A base v S s) (hfront : s.nr 0 = v) (hpred : s.nr 70 = u)
    (hz : s.nr 30 = 0) (hq : s.nr 57 = A.q) (hs : s.nr 59 = (A.d + 4) * A.I.graph.n)
    (hpgf : ∀ r : Fin A.d, s.rm (s.nr 49 + 4 + r.val) = clockPGF A r u v) :
    ∃ out, Run input (prepareEdge A.d) s out (6 * A.d + 12) ∧ Loaded (edgeParameters A S u v s.rm) out ∧
      out.nr 50 = scanAddress base A.I.graph.n A.q u S.counts ∧ out.nr 56 = 0 ∧
      (∀ j, j ≠ 50 → j ≠ 56 → j ≠ 60 → j ≠ 67 → out.nr j = s.nr j) ∧
      out.nm = s.nm ∧ out.rm = s.rm := by
  let p := positioned A.d input s
  obtain ⟨hp, hempty, hpn, hpr, hpm, hprm⟩ := position_fields A.d input s
  obtain ⟨out, hrun, hcoeff, hnr, hrr, hnm, hrm⟩ := divide_run input A.d p
  have regs (j : ℕ) (ha : j ≠ 50) (hb : j ≠ 56) (hc : j ≠ 60) (hd : j ≠ 67) :
      out.nr j = s.nr j := (hnr j hd).trans (hpn j ha hb hc)
  have hrs (j : ℕ) (hh : j < 100) (hne : j ≠ 6) : out.rr j = s.rr j :=
    (hrr j hne (fun r _ => by unfold coeffReg CandidateRAM.current; omega)).trans (congrFun hpr j)
  have h49 : p.nr 49 = s.nr 49 := hpn 49 (by decide) (by decide) (by decide)
  have hcost : 2 * A.d + 12 + 4 * A.d = 6 * A.d + 12 := by omega
  refine ⟨out, hcost ▸ Run.seq (position_run A.d input s) hrun, ?_, ?_, (hnr 56 (by decide)).trans hempty,
    regs, hnm.trans hpm, hrm.trans hprm⟩
  · refine ⟨(regs 30 (by decide) (by decide) (by decide) (by decide)).trans hz,
      (regs 31 (by decide) (by decide) (by decide) (by decide)).trans hcur.one,
      (regs 57 (by decide) (by decide) (by decide) (by decide)).trans hq,
      (regs 59 (by decide) (by decide) (by decide) (by decide)).trans hs, (hrs 12 (by decide) (by decide)).trans hcur.factor,
      ?_, ?_, hrm.trans hprm⟩
    · intro r; have hh := state_large r.val
      exact (regs _ (by omega) (by omega) (by omega) (by omega)).trans (hcur.counts r)
    · intro r
      have he := hcoeff r.val r.isLt
      change p.rm = s.rm at hprm
      change p.rr = s.rr at hpr
      rw [hpr, hprm, h49, hcur.coeff, hpgf] at he
      exact he
  · rw [hfront, hpred, hcur.address] at hp
    have he := (hnr 50 (by decide)).trans hp
    simp only [scanAddress, Nat.mul_add] at he ⊢
    omega

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured CandidateRAM

def adoptOps (r : ℕ) : List Atom :=
  [⟨.natCopy (stateReg r) (best r), trivial⟩, ⟨.realCopy (stateReg r) (best r), trivial⟩]
def adoptLanes : ℕ → Cmd
  | 0 => .skip
  | d + 1 => .seq (adoptLanes d) (.atoms (adoptOps d))
def commitHead : List Atom := [⟨.natCopy 49 55, trivial⟩, ⟨.natCopy 0 70, trivial⟩]
def edgeCmd (d : ℕ) : Cmd := .seq (prepareEdge d)
  (.seq (sweep d ((List.finRange d).map Fin.val)) (.seq (adoptLanes d) (.atoms commitHead)))

theorem adopt_run (input : RAMInput) (d : ℕ) (s : Store) :
    ∃ t, Run input (adoptLanes d) s t (2 * d) ∧
      (∀ r < d, t.nr (stateReg r) = s.nr (best r) ∧ t.rr (stateReg r) = s.rr (best r)) ∧
      (∀ j, (∀ r < d, j ≠ stateReg r) → t.nr j = s.nr j ∧ t.rr j = s.rr j) ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  induction d with
  | zero => exact ⟨s, Run.skip s, by simp, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | succ d ih =>
    obtain ⟨p, hr, hs, hf, hnm, hrm⟩ := ih
    let t : Store := {p with
      nr := Function.update p.nr (stateReg d) (p.nr (best d))
      rr := Function.update p.rr (stateReg d) (p.rr (best d))}
    have hnew : Run input (.atoms (adoptOps d)) p t 2 := run_atoms input (adoptOps d) p
    have hb := hf (best d) (fun r _ => by unfold best stateReg current; omega)
    have hcost : 2 * d + 2 = 2 * (d + 1) := by omega
    refine ⟨t, hcost ▸ Run.seq hr hnew, ?_, ?_, hnm, hrm⟩
    · intro r hrd
      by_cases he : r = d
      · subst r; simpa [t] using hb
      · have hn : stateReg r ≠ stateReg d := fun h => he (state_inj.mp h)
        simpa [t, Function.update_of_ne hn] using hs r (by omega)
    · intro j hj
      have hn := hj d (by omega)
      simpa [t, Function.update_of_ne hn] using hf j (fun r hr => hj r (by omega))

theorem incumbent_fields (d : ℕ) (s : Store) (x : Sample d) (h : incumbent d s = some x) :
    s.nr 55 = x.address ∧ ∀ r : Fin d, s.nr (best r.val) = x.amounts r ∧ s.rr (best r.val) = x.factors r := by
  unfold incumbent at h
  split at h
  · cases h
  · have he := Option.some.inj h
    exact ⟨congrArg Sample.address he, fun r =>
      ⟨congrArg (fun z => Sample.amounts z r) he, congrArg (fun z => Sample.factors z r) he⟩⟩

theorem fixed_stride (d : ℕ) (rs : List ℕ) (r : ℕ) : fixedNat d rs (strideReg r) := by
  unfold fixedNat strideReg current best counterReg
  exact ⟨by omega, by omega, by omega, fun _ _ => by omega, fun _ _ => by dsimp [current]; omega⟩

theorem edge_transition {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (S : RetrievalState A.d)
    (u v base : ℕ) (input : RAMInput) (s : Store) (hcur : Cursor A base v S s)
    (hfront : s.nr 0 = v) (hpred : s.nr 70 = u) (hz : s.nr 30 = 0)
    (hq : s.nr 57 = A.q) (hs : s.nr 59 = (A.d + 4) * A.I.graph.n)
    (hpgf : ∀ r : Fin A.d, s.rm (s.nr 49 + 4 + r.val) = clockPGF A r u v)
    (htable : ∀ i : Fin A.d → ℕ, (∀ r, i r < A.q) →
      s.rm (scanAddress base A.I.graph.n A.q u i) = 1 - (T u i).value)
    (a : Fin A.d → ℕ) (rest : List (Fin A.d → ℕ)) (hbox : rectangle A S.counts = a :: rest) :
    let b := selectMin (incrementScore A T S u v) (a :: rest) a
    ∃ out cost, Run input (edgeCmd A.d) s out cost ∧ Cursor A base u (edgeState A S u v b) out ∧
      out.nr 0 = u ∧ (∀ j, 0 < j → j < 49 → out.nr j = s.nr j) ∧
      out.nr 57 = A.q ∧ out.nr 59 = (A.d + 4) * A.I.graph.n ∧ out.nm = s.nm ∧ out.rm = s.rm ∧
      cost ≤ (13 * A.d + 25) * (2 ^ A.d * (A.q + 1) ^ A.d) := by
  let rs := (List.finRange A.d).map Fin.val
  let b := selectMin (incrementScore A T S u v) (a :: rest) a
  let D := edgeParameters A S u v s.rm
  obtain ⟨p, hp, hl, ha, hzero, hreg, hpn, hpr⟩ :=
    prepare_edge_run A S u v base input s hcur hfront hpred hz hq hs hpgf
  obtain ⟨w, n, hw, hchoice, hf, hc⟩ := edge_sweep A T S u v base s.rm a rest hbox htable input p hl ha hzero
  have hwload : Loaded D w := hl.frame hf
  obtain ⟨haddr, hlanes⟩ := incumbent_fields A.d w _ hchoice
  obtain ⟨l, hlrun, hadopt, hkeep, hln, hlr⟩ := adopt_run input A.d w
  let out : Store := {l with nr := Function.update (Function.update l.nr 49 (l.nr 55)) 0 (l.nr 70)}
  have hout : Run input (.atoms commitHead) l out 2 := run_atoms input commitHead l
  have low (j : ℕ) (hj : j < 100) := hkeep j (fun r _ => by have := state_large r; omega)
  have hou (j : ℕ) (h0 : j ≠ 0) (h49 : j ≠ 49) : out.nr j = l.nr j := by
    simp [out, Function.update_of_ne h0, Function.update_of_ne h49]
  have hnsmall (j : ℕ) (hj : j < 100) (ha : j ≠ 50) (hb : j ≠ 55) (hc : j ≠ 56)
      (hd : j ≠ 60) (he : j ≠ 67) : l.nr j = s.nr j :=
    (low j hj).1.trans ((hf.natRegs _ (fixed_small _ _ j hj ha hb hc)).trans (hreg j ha hc hd he))
  have hnon : 1 ≤ 2 ^ A.d * (A.q + 1) ^ A.d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))
  refine ⟨out, _, Run.seq hp (Run.seq hw (Run.seq hlrun hout)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · have ht : out.nr 49 = w.nr 55 := by simp [out, (low 55 (by decide)).1]
      exact ht.trans haddr
    · intro r
      have hh := state_large r.val
      exact (hou _ (by omega) (by omega)).trans ((hadopt r.val r.isLt).1.trans (hlanes r).1)
    · intro r
      have he := (hadopt r.val r.isLt).2.trans (hlanes r).2
      change l.rr (stateReg r.val) = clockZ A ^ b r * S.H r / clockPGF A r u v
      simpa only [sample, D, edgeParameters, mul_div_assoc] using he
    · intro r
      have hh := stride_large r.val
      exact (hou _ (by omega) (by omega)).trans
        ((hkeep _ (fun j _ => stride_ne_state r.val j)).1.trans
          ((hf.natRegs _ (fixed_stride _ _ _)).trans ((hreg _ (by omega) (by omega) (by omega) (by omega)).trans (hcur.strides r))))
    · exact (low 12 (by decide)).2.trans hwload.factor
    · exact (hou _ (by decide) (by decide)).trans ((low 31 (by decide)).1.trans hwload.one)
  · simpa [out] using (hnsmall 70 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpred
  · intro j h1 h2
    exact (hou _ (by omega) (by omega)).trans (hnsmall j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact (hou _ (by decide) (by decide)).trans ((low 57 (by decide)).1.trans hwload.bound)
  · exact (hou _ (by decide) (by decide)).trans ((low 59 (by decide)).1.trans hwload.step)
  · exact hln.trans (hf.natMem.trans hpn)
  · exact hlr.trans (hf.realMem.trans hpr)
  · have hh := Nat.mul_le_mul_left (8 * A.d + 14) hnon
    nlinarith

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.ParentQuery
open Mission.Structured
open Mission.Query (StoresList prependCmd prependResult prepend_run storesList_cons storesList_map)

inductive Walk (n source : ℕ) (next : ℕ → ℕ) : ℕ → List ℕ → Prop where
  | sourcePath : Walk n source next source [source]
  | edge {v u : ℕ} {P : List ℕ} (hv : v < n) (hne : v ≠ source)
      (hp : next v = u + 1) (hP : Walk n source next u P) : Walk n source next v (P ++ [v])

def readParent (k : ℕ) : List Atom :=
  [ ⟨.natOp .add 36 0 0, trivial⟩,
    ⟨.natOp .add 36 36 36, trivial⟩,
    ⟨.natConst 37 (34 + 2 * k), trivial⟩,
    ⟨.natOp .add 36 37 36, trivial⟩,
    ⟨.loadNat 0 36, trivial⟩,
    ⟨.natOp .sub 0 0 31, trivial⟩ ]

def stopCmd : Cmd := .atom ⟨.natConst 40 0, trivial⟩
def body (k : ℕ) : Cmd :=
  .seq prependCmd (.branch (.nat .eq 0 5) stopCmd (.atoms (readParent k)))
def loopCmd (k : ℕ) : Cmd := .loop (.nat .lt 30 40) (body k)
def found : Atom := ⟨.natConst 1 1, trivial⟩

structure Output (P : List ℕ) (s : Store) : Prop where
  count : s.nr 2 = P.length
  vertices : StoresList s.nm (s.nr 3) P

structure Registers (source v : ℕ) (s : Store) : Prop where
  front : s.nr 0 = v
  sourceReg : s.nr 5 = source
  zero : s.nr 30 = 0
  one : s.nr 31 = 1
  live : s.nr 40 = 1

def Parents (k n : ℕ) (next : ℕ → ℕ) (s : Store) : Prop :=
  ∀ v < n, s.nm (targetSlot k v + 2) = next v

theorem output_prepend (s : Store) (v : ℕ) (P : List ℕ) (hs : s.nr 0 = v)
    (h : Output P s) (hb : 0 < s.nr 3) : Output (v :: P) (prependResult s) := by
  constructor
  · simp [prependResult, h.count]
  · simpa [prependResult, hs] using storesList_cons s.nm (s.nr 3) v P hb h.vertices

theorem registers_prepend {source v : ℕ} {s : Store} (h : Registers source v s) :
    Registers source v (prependResult s) := by
  rcases h with ⟨h₀, h₅, hz, h₁, hl⟩
  constructor <;> simp [prependResult, *]

theorem parents_prepend {k n : ℕ} {next : ℕ → ℕ} {s : Store}
    (h : Parents k n next s) (hb : targetSlot k n < s.nr 3) :
    Parents k n next (prependResult s) := by
  intro v hv
  have ha : targetSlot k v + 2 ≠ s.nr 3 - 1 := by unfold targetSlot at *; omega
  simpa only [prependResult, Function.update_of_ne ha] using h v hv

theorem read_fields (input : RAMInput) (k : ℕ) (s : Store) (hone : s.nr 31 = 1) :
    let t := evalAtoms input (readParent k) s
    t.nr 0 = s.nm (targetSlot k (s.nr 0) + 2) - 1 ∧
    t.nr 2 = s.nr 2 ∧ t.nr 3 = s.nr 3 ∧ t.nr 5 = s.nr 5 ∧
    t.nr 30 = s.nr 30 ∧ t.nr 31 = 1 ∧ t.nr 40 = s.nr 40 ∧ t.nm = s.nm := by
  have he : 34 + 2 * k + (s.nr 0 + s.nr 0 + (s.nr 0 + s.nr 0)) = targetSlot k (s.nr 0) + 2 := by
    unfold targetSlot; omega
  simp [readParent, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, hone, he]

theorem stop_run (input : RAMInput) (s : Store) :
    Run input stopCmd s {s with nr := Function.update s.nr 40 0} 1 := by
  exact Run.atom ⟨.natConst 40 0, trivial⟩ s

theorem walk_run {n source : ℕ} {next : ℕ → ℕ} {v : ℕ} {P : List ℕ}
    (k : ℕ) (input : RAMInput) (hwalk : Walk n source next v P)
    (s : Store) (suffix : List ℕ) (hreg : Registers source v s) (hp : Parents k n next s)
    (hbuf : Output suffix s) (hroom : targetSlot k n + P.length ≤ s.nr 3) :
    ∃ t steps, Run input (loopCmd k) s t steps ∧ Output (P ++ suffix) t ∧
      steps ≤ 16 * P.length + 1 := by
  induction hwalk generalizing s suffix with
  | sourcePath =>
    have hb : 0 < s.nr 3 := by simp only [List.length_singleton] at hroom; omega
    let p := prependResult s
    let t : Store := {p with nr := Function.update p.nr 40 0}
    have hrp : Registers source source p := registers_prepend hreg
    have hpp : Output (source :: suffix) p := output_prepend s source suffix hreg.front hbuf hb
    have hg : (Guard.nat .lt 30 40).eval s = true := by simp [Guard.eval, natTest, hreg.zero, hreg.live]
    have hs : (Guard.nat .eq 0 5).eval p = true := by simp [Guard.eval, natTest, hrp.front, hrp.sourceReg]
    have he : (Guard.nat .lt 30 40).eval t = false := by simp [t, Guard.eval, natTest]
    have hbody : Run input (body k) s t 6 :=
      Run.seq (prepend_run input s hreg.one) (Run.branchTrue hs (stop_run input p))
    refine ⟨t, 9, Run.loopTrue hg hbody (Run.loopFalse he), ?_, by norm_num⟩
    exact ⟨by simpa [t] using hpp.count, by simpa [t] using hpp.vertices⟩
  | @edge v u Q hv hne hparent hQ ih =>
    have hlength : (Q ++ [v]).length = Q.length + 1 := by simp
    have hbase : targetSlot k n < s.nr 3 := by omega
    have hb : 0 < s.nr 3 := by omega
    let p := prependResult s
    have hrp : Registers source v p := registers_prepend hreg
    have hop : Output (v :: suffix) p := output_prepend s v suffix hreg.front hbuf hb
    have hpp : Parents k n next p := parents_prepend hp hbase
    let w := evalAtoms input (readParent k) p
    obtain ⟨hcur, h2, h3, h5, h30, h31, h40, hmem⟩ := read_fields input k p hrp.one
    have hf : w.nr 0 = u := by simpa only [hrp.front, hpp v hv, hparent, Nat.add_sub_cancel] using hcur
    have hrw : Registers source u w := ⟨hf, h5.trans hrp.sourceReg, h30.trans hrp.zero, h31, h40.trans hrp.live⟩
    have how : Output (v :: suffix) w := ⟨h2.trans hop.count, by simpa only [w, h3, hmem] using hop.vertices⟩
    have hpw : Parents k n next w := fun a ha => (congrFun hmem _).trans (hpp a ha)
    have hbasew : w.nr 3 = s.nr 3 - 1 := h3.trans (by simp [p, prependResult])
    obtain ⟨t, steps, htail, hout, hc⟩ := ih w (v :: suffix) hrw hpw how (by omega)
    have hg : (Guard.nat .lt 30 40).eval s = true := by simp [Guard.eval, natTest, hreg.zero, hreg.live]
    have hs : (Guard.nat .eq 0 5).eval p = false := by simp [Guard.eval, natTest, hrp.front, hrp.sourceReg, hne]
    have hadv : Run input (Cmd.atoms (readParent k)) p w 6 := run_atoms input (readParent k) p
    have hbody : Run input (body k) s w 10 := Run.seq (prepend_run input s hreg.one) (Run.branchFalse hs hadv)
    exact ⟨t, 1 + 10 + 1 + steps, Run.loopTrue hg hbody htail,
      by simpa only [List.append_assoc, List.singleton_append] using hout, by omega⟩

end NearLinearRSP.TwoResources.Supplement.ParentQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured
open Mission.Query (prependResult)

def Image {k : ℕ} (A : ClockCall k) (base : ℕ) (s : Store) : Prop :=
  ∀ v ∈ incidentVertices A.I, ∀ i : Fin A.d → ℕ, (∀ j, i j < A.q) →
    let addr := scanAddress base A.I.graph.n A.q v i
    let c := constructTable A v i
    s.rm addr = 1 - c.value ∧ s.nm addr = multiParentTag c.parent ∧
      s.nm (addr + 1) = multiParentPayload c.parent ∧
      ∀ u, c.parent = .edge u → ∀ j : Fin A.d, s.rm (addr + 4 + j.val) = clockPGF A j u v

theorem encoded_image {k : ℕ} (I : MultiInstance k) (ε : ℝ) (snap : RAMState)
    (hs : EncodesMultiOutput I ε snap) (r : ℕ) (A : ClockCall k) (ha : (outerCalls I ε)[r]? = some A)
    (hi : A.I = I) (s : Store) (hn : s.nm = snap.nm) (hr : s.rm = snap.rm) :
    Image A (callBase I ε r) s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, htable⟩ := hs
  intro v hv i hvalid
  dsimp only
  rw [hi] at hv
  obtain ⟨hv0, ht, hp, _, hg⟩ := (htable r A ha).2.2 v hv i hvalid
  simpa only [scanAddress, hn, hr, hi] using And.intro hv0 (And.intro ht (And.intro hp hg))

theorem scanAddress_inside {k : ℕ} (A : ClockCall k) (base v : ℕ) (hv : v < A.I.graph.n)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (x : ℕ) (hx : x < A.d + 4) :
    scanAddress base A.I.graph.n A.q v i + x < extent A base := by
  have hr := vectorIndex_lt i hi
  have hm := Nat.mul_le_mul_right A.I.graph.n (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hm
  have hrow : vectorIndex A.q i * A.I.graph.n + v + 1 ≤ A.q ^ A.d * A.I.graph.n := by omega
  have hn := Nat.mul_le_mul_left (A.d + 4) hrow
  rw [Nat.mul_add, Nat.mul_one] at hn
  unfold scanAddress extent
  have he : (A.d + 4) * A.I.graph.n * A.q ^ A.d = (A.d + 4) * (A.q ^ A.d * A.I.graph.n) := by ring
  rw [he]; omega

theorem Image.frame {k : ℕ} {A : ClockCall k} {base : ℕ} {s t : Store} (h : Image A base s)
    (hn : t.nm = s.nm) (hr : t.rm = s.rm) : Image A base t := by
  intro v hv i hi
  simpa only [hn, hr] using h v hv i hi

theorem Image.prepend {k : ℕ} {A : ClockCall k} {base : ℕ} {s : Store} (h : Image A base s)
    (hb : extent A base < s.nr 3) : Image A base (prependResult s) := by
  intro v hv i hi
  let a := scanAddress base A.I.graph.n A.q v i
  have h0 : a < extent A base := by simpa [a] using scanAddress_inside A base v (incident_valid A.I v hv) i hi 0 (by omega)
  have h1 : a + 1 < extent A base := scanAddress_inside A base v (incident_valid A.I v hv) i hi 1 (by omega)
  have hne : a ≠ s.nr 3 - 1 := by omega
  have hne1 : a + 1 ≠ s.nr 3 - 1 := by omega
  change s.rm a = _ ∧ (prependResult s).nm a = _ ∧ (prependResult s).nm (a + 1) = _ ∧ _
  simpa only [prependResult, Function.update_of_ne hne, Function.update_of_ne hne1] using h v hv i hi

structure Ready {k : ℕ} (A : ClockCall k) (base v : ℕ) (S : RetrievalState A.d) (s : Store) : Prop where
  cursor : Cursor A base v S s
  front : s.nr 0 = v
  source : s.nr 5 = A.I.source
  zero : s.nr 30 = 0
  live : s.nr 40 = 1
  q : s.nr 57 = A.q
  step : s.nr 59 = (A.d + 4) * A.I.graph.n
  output : ParentQuery.Output S.path s
  table : Image A base s

def readParentOps : List Atom :=
  [⟨.loadNat 71 49, trivial⟩, ⟨.natOp .add 67 49 31, trivial⟩, ⟨.loadNat 70 67, trivial⟩]
noncomputable def parentRead (input : RAMInput) (s : Store) : Store := evalAtoms input readParentOps s

theorem read_parent_fields (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) :
    let t := parentRead input s
    t.nr 71 = s.nm (s.nr 49) ∧ t.nr 70 = s.nm (s.nr 49 + 1) ∧
      (∀ j, j ≠ 67 → j ≠ 70 → j ≠ 71 → t.nr j = s.nr j) ∧ t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  simp +contextual [parentRead, readParentOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, hone]

theorem ready_parentRead {k : ℕ} {A : ClockCall k} {base v : ℕ} {S : RetrievalState A.d} {s : Store}
    (h : Ready A base v S s) (input : RAMInput) (hv : v ∈ incidentVertices A.I) (hi : ∀ r, S.counts r < A.q) :
    let t := parentRead input s
    Ready A base v S t ∧ t.nr 71 = multiParentTag (constructTable A v S.counts).parent ∧
      t.nr 70 = multiParentPayload (constructTable A v S.counts).parent ∧ t.nr 3 = s.nr 3 := by
  obtain ⟨htag, hparent, hnr, hrr, hnm, hrm⟩ := read_parent_fields input s h.cursor.one
  obtain ⟨_, htag', hparent', _⟩ := h.table v hv S.counts hi
  have low (j : ℕ) (hj : j < 67) := hnr j (by omega) (by omega) (by omega)
  refine ⟨⟨?_, (low 0 (by decide)).trans h.front, (low 5 (by decide)).trans h.source,
    (low 30 (by decide)).trans h.zero, (low 40 (by decide)).trans h.live, (low 57 (by decide)).trans h.q,
    (low 59 (by decide)).trans h.step, ?_, h.table.frame hnm hrm⟩, ?_, ?_, low 3 (by decide)⟩
  · refine ⟨(low 49 (by decide)).trans h.cursor.address, ?_, fun r => (congrFun hrr _).trans (h.cursor.coeff r), ?_,
      (congrFun hrr _).trans h.cursor.factor, (low 31 (by decide)).trans h.cursor.one⟩
    · intro r; have hh := state_large r.val
      exact (hnr _ (by omega) (by omega) (by omega)).trans (h.cursor.counts r)
    · intro r; have hh := stride_large r.val
      exact (hnr _ (by omega) (by omega) (by omega)).trans (h.cursor.strides r)
  · exact ⟨(low 2 (by decide)).trans h.output.count, by simpa only [hnm, low 3 (by decide)] using h.output.vertices⟩
  · exact htag.trans (h.cursor.address ▸ htag')
  · exact hparent.trans (h.cursor.address ▸ hparent')

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
open scoped NNReal BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem quadratic_feasible_mean {k : ℕ} (A : ClockCall k)
    (hk : 1 ≤ k) (hδ : 0 < A.δ) (hδ1 : A.δ ≤ 1) (M : ℝ)
    (hM : M ≤ (A.q : ℝ) / (1 + A.δ / 2)) :
    quadratic A.q M 0 M ≤ 1 / (8 * (k : ℝ)) := by
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hq : (0 : ℝ) < A.q := by exact_mod_cast ticks_pos k A.δ hk0 hδ
  have hbase : (A.q : ℝ) / (1 + A.δ / 2) < A.q :=
    div_lt_self hq (by linarith)
  have hgap := sub_pos.mpr hbase
  rw [quadratic_initial]
  apply le_trans (div_le_div₀ (by positivity) hM (sq_pos_of_pos hgap) ?_)
  · have hsize : 128 * (k : ℝ) ≤ (A.q : ℝ) * A.δ ^ 2 := by
      have hh := ticks_sufficient k A.δ hδ
      have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      change 512 * (k : ℝ) ≤ (A.q : ℝ) * A.δ ^ 2 at hh
      linarith
    exact RSP.Tails.completeness_ratio_le A.q A.δ k hk0 hq hδ hδ1 hsize
  · nlinarith [sq_nonneg ((A.q : ℝ) / (1 + A.δ / 2) - M),
      mul_nonneg hgap.le (sub_nonneg.mpr hM)]

theorem quadratic_vector_initial_bound {k : ℕ} (A : ClockCall k)
    (hk : 1 ≤ k) (hδ : 0 < A.δ) (hδ1 : A.δ ≤ 1) (M : Fin A.d → ℝ)
    (hM : ∀ r, M r ≤ (A.q : ℝ) / (1 + A.δ / 2)) :
    (∑ r, quadratic A.q (M r) 0 (M r)) ≤ 1 / 8 := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hd : (A.d : ℝ) ≤ k := by exact_mod_cast clockCoordinates_length_le A.I
  calc
    (∑ r, quadratic A.q (M r) 0 (M r)) ≤ ∑ _r : Fin A.d, 1 / (8 * (k : ℝ)) :=
      Finset.sum_le_sum (fun r _ => quadratic_feasible_mean A hk hδ hδ1 (M r) (hM r))
    _ = (A.d : ℝ) * (1 / (8 * (k : ℝ))) := by simp
    _ ≤ (k : ℝ) * (1 / (8 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = 1 / 8 := by field_simp

theorem expectation_le_quadratic {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (T : MultiTable A.d)
    (u v : ℕ) (i : Fin A.d → ℕ) (M r : Fin A.d → ℝ)
    (hM : ∀ j, M j < (A.q : ℝ)) (hr : ∀ j, 0 ≤ r j)
    (hD : ∀ a : Fin A.d → ℕ, value A T u (fun j => i j + a j) ≤
      ∑ j, quadratic A.q (M j) (i j + a j) (r j)) :
    expectation A T u v i ≤
      ∑ j, quadratic A.q (M j) (i j) (r j + clockMean A j u v) := by
  classical
  let e : Fin A.d → ℝ≥0 := fun j => ⟨clockMean A j u v, clockMean_nonneg A hδ hL j u v⟩
  let R := (rectangle A i).toFinset
  have hG := quadratic_vector_hasSum (A.q : ℝ) M (fun j => (i j : ℝ)) r e hr
  have hG' : HasSum (fun a : Fin A.d → ℕ => incrementMass A u v a *
      ∑ j, quadratic A.q (M j) ((i j : ℝ) + a j) (r j))
      (∑ j, quadratic A.q (M j) (i j) (r j + clockMean A j u v)) := hG
  have h := rectangle_comparison R (incrementMass A u v)
    (fun a => value A T u (fun j => i j + a j))
    (fun a => ∑ j, quadratic A.q (M j) ((i j : ℝ) + a j) (r j))
    (∑ j, quadratic A.q (M j) (i j) (r j + clockMean A j u v))
    (incrementMass_nonneg A hδ hL u v) (incrementMass_hasSum A hδ hL u v) hG'
    (fun a _ => by simpa only [Nat.cast_add] using hD a) ?_
  · simpa only [R, expectation, List.sum_toFinset _ (rectangle_nodup A i)] using h
  · intro a ha
    have hn : ¬∀ j, i j + a j < A.q := by
      intro hj
      exact ha (List.mem_toFinset.mpr ((rectangle_mem A i a).mpr hj))
    push_neg at hn
    obtain ⟨j, hj⟩ := hn
    have hj' : (A.q : ℝ) ≤ (i j : ℝ) + a j := by exact_mod_cast hj
    exact (quadratic_saturated A.q (M j) ((i j : ℝ) + a j) (r j) (hM j) hj' (hr j)).trans
      (Finset.single_le_sum (fun l _ => quadratic_nonneg A.q (M l) ((i l : ℝ) + a l) (r l) (hr l))
        (Finset.mem_univ j))

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
open scoped NNReal BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem callEdges_incident {k : ℕ} (A : ClockCall k) (u v : ℕ)
    (he : (u, v) ∈ callEdges A) :
    u ∈ incidentVertices A.I ∧ v ∈ incidentVertices A.I := by
  have hg : (u, v) ∈ A.I.graph.edges :=
    List.mem_of_mem_filter (List.mem_of_mem_filter he)
  constructor
  · simp only [incidentVertices, List.mem_eraseDups, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨(u, v), hg, by simp⟩
  · simp only [incidentVertices, List.mem_eraseDups, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨(u, v), hg, by simp⟩

theorem pathWeight_append_singleton (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) (u v : ℕ)
    (hu : P.getLast? = some u) :
    pathWeight w (P ++ [v]) = pathWeight w P + (w u v : ℝ) := by
  induction P with
  | nil => simp at hu
  | cons a P ih =>
    cases P with
    | nil =>
      have ha : a = u := by simpa using hu
      subst a
      simp [pathWeight]
    | cons b bs =>
      have hu' : (b :: bs).getLast? = some u := by simpa using hu
      simp only [List.cons_append, pathWeight_cons_cons]
      have hh := ih hu'
      simp only [List.cons_append] at hh
      rw [hh]
      ring

theorem clockRate_nonneg {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (r : Fin A.d) : 0 ≤ clockRate A r := by
  have hb := clockBudget_pos A.I A.L hL r
  unfold clockRate
  positivity

noncomputable def pathMean {k : ℕ} (A : ClockCall k) (P : List ℕ) (r : Fin A.d) : ℝ :=
  clockRate A r * pathWeight (coordinateWeight A.I (A.coords.get r)) P

theorem pathMean_nonneg {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L)
    (P : List ℕ) (r : Fin A.d) : 0 ≤ pathMean A P r :=
  mul_nonneg (clockRate_nonneg A hδ hL r) (pathWeight_nonneg _ _)

theorem pathMean_append {k : ℕ} (A : ClockCall k) (P : List ℕ) (u v : ℕ)
    (hu : P.getLast? = some u) (r : Fin A.d) :
    pathMean A (P ++ [v]) r = pathMean A P r + clockMean A r u v := by
  unfold pathMean
  rw [pathWeight_append_singleton _ P u v hu, mul_add]
  rfl

theorem source_quadratic_bound {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (M : Fin A.d → ℝ)
    (hM : ∀ r, M r < (A.q : ℝ)) (i : Fin A.d → ℕ) :
    value A (constructTable A) A.I.source i ≤ ∑ r, quadratic A.q (M r) (i r) 0 := by
  classical
  by_cases hi : ∀ r, i r < A.q
  · rw [value_of_valid A (constructTable A) A.I.source i hi, constructTable_source A hδ hL i hi]
    exact Finset.sum_nonneg (fun r _ => quadratic_nonneg _ _ _ _ le_rfl)
  · have hh : ∃ r, A.q ≤ i r := by simpa using hi
    obtain ⟨r, hr⟩ := hh
    have hr' : (A.q : ℝ) ≤ (i r : ℝ) := by exact_mod_cast hr
    exact (value_range A (constructTable A) (constructTable_range A hδ hL) _ _).2.trans
      ((quadratic_saturated A.q (M r) (i r) 0 (hM r) hr' le_rfl).trans
        (Finset.single_le_sum (fun s _ => quadratic_nonneg A.q (M s) (i s) 0 le_rfl) (Finset.mem_univ r)))

theorem constructTable_path_bound {k : ℕ} (A : ClockCall k)
    (hδ : 0 < A.δ) (hL : 0 < A.L) (P : List ℕ) (t : ℕ)
    (hhead : P.head? = some A.I.source) (hlast : P.getLast? = some t)
    (hchain : P.IsChain (fun u v => (u, v) ∈ callEdges A))
    (M : Fin A.d → ℝ) (hM : ∀ r, M r < (A.q : ℝ)) (i : Fin A.d → ℕ) :
    value A (constructTable A) t i ≤ ∑ r, quadratic A.q (M r) (i r) (pathMean A P r) := by
  induction P using List.reverseRecOn generalizing t i with
  | nil => simp at hhead
  | append_singleton P v ih =>
    have ht : v = t := by simpa using hlast
    subst t
    by_cases hnil : P = []
    · subst P
      have hv : v = A.I.source := by simpa using hhead
      subst v
      simpa [pathMean, pathWeight] using source_quadratic_bound A hδ hL M hM i
    · let u := P.getLast hnil
      have hu : P.getLast? = some u := List.getLast?_eq_some_getLast hnil
      have he : (u, v) ∈ callEdges A :=
        (List.isChain_append.mp hchain).2.2 u hu v (by simp)
      have hpre : P.head? = some A.I.source := by
        cases hp : P with
        | nil => exact (hnil hp).elim
        | cons a ps => simpa [hp] using hhead
      have hpred (j : Fin A.d → ℕ) := ih u hpre hu hchain.left_of_append j
      have hb := expectation_le_quadratic A hδ hL (constructTable A) u v i M (pathMean A P)
        hM (pathMean_nonneg A hδ hL P) (fun a => by simpa only [Nat.cast_add] using hpred (fun r => i r + a r))
      have heI := callEdges_incident A u v he
      have hd := constructTable_bellman A hδ hL i u v heI.1 heI.2 he
      have heq : (fun r => pathMean A P r + clockMean A r u v) = pathMean A (P ++ [v]) := by
        funext r
        exact (pathMean_append A P u v hu r).symm
      simpa only [← pathMean_append A P u v hu] using hd.trans hb

theorem accepts_of_path {k : ℕ} (A : ClockCall k) (hk : 1 ≤ k)
    (hδ : 0 < A.δ) (hδ1 : A.δ ≤ 1) (hL : 0 < A.L) (P : List ℕ) (t : ℕ)
    (hhead : P.head? = some A.I.source) (hlast : P.getLast? = some t)
    (hchain : P.IsChain (fun u v => (u, v) ∈ callEdges A))
    (hbudget : ∀ r : Fin A.d, pathWeight (coordinateWeight A.I (A.coords.get r)) P ≤
      coordinateBudget A.I A.L (A.coords.get r)) : accepts A t = true := by
  have hq : (0 : ℝ) < A.q := by
    exact_mod_cast ticks_pos k A.δ (lt_of_lt_of_le Nat.zero_lt_one hk) hδ
  have hM (r : Fin A.d) : pathMean A P r ≤ (A.q : ℝ) / (1 + A.δ / 2) := by
    have hB := clockBudget_pos A.I A.L hL r
    have hB0 : coordinateBudget A.I A.L (A.coords.get r) ≠ 0 := hB.ne'
    calc
      _ ≤ clockRate A r * coordinateBudget A.I A.L (A.coords.get r) :=
        mul_le_mul_of_nonneg_left (hbudget r) (clockRate_nonneg A hδ hL r)
      _ = _ := by unfold clockRate; field_simp [hB0]
  have hMlt (r : Fin A.d) : pathMean A P r < (A.q : ℝ) :=
    (hM r).trans_lt (div_lt_self hq (by linarith))
  have hb := constructTable_path_bound A hδ hL P t hhead hlast hchain
    (pathMean A P) hMlt (fun _ => 0)
  have hi := quadratic_vector_initial_bound A hk hδ hδ1 (pathMean A P) hM
  simp only [Nat.cast_zero] at hb
  have hacc : value A (constructTable A) t (fun _ => 0) ≤ 1 / 4 := by
    exact (hb.trans hi).trans (by norm_num)
  simpa only [accepts, decide_eq_true_eq] using hacc

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped NNReal

namespace NearLinearRSP.TwoResources.Supplement

theorem chain_and {α : Type*} (R S : α → α → Prop) (P : List α)
    (hR : P.IsChain R) (hS : P.IsChain S) : P.IsChain (fun u v => R u v ∧ S u v) := by
  induction P with
  | nil => simp
  | cons u P ih =>
    cases P with
    | nil => simp
    | cons v vs =>
      exact List.isChain_cons_cons.mpr ⟨⟨hR.rel, hS.rel⟩, ih hR.tail hS.tail⟩

theorem chain_forall {α β : Type*} (R : β → α → α → Prop) (P : List α)
    (hR : ∀ b, P.IsChain (R b)) : P.IsChain (fun u v => ∀ b, R b u v) := by
  induction P with
  | nil => simp
  | cons u P ih =>
    cases P with
    | nil => simp
    | cons v vs =>
      exact List.isChain_cons_cons.mpr ⟨fun b => (hR b).rel, ih (fun b => (hR b).tail)⟩

theorem nodup_chain_ne {α : Type*} (P : List α) (hP : P.Nodup) :
    P.IsChain (fun u v => u ≠ v) := by
  induction P with
  | nil => simp
  | cons u P ih =>
    cases P with
    | nil => simp
    | cons v vs =>
      have hn := List.nodup_cons.mp hP
      refine List.isChain_cons_cons.mpr ⟨?_, ih hn.2⟩
      intro he
      exact hn.1 (by simp [he])

theorem feasible_simple {k : ℕ} (I : MultiInstance k) (t : ℕ) (P : List ℕ)
    (hP : ExactFeasible I t P) :
    ∃ Q, ExactFeasible I t Q ∧ Q.Nodup ∧ Q.length ≤ I.graph.n ∧
      pathWeight I.length Q ≤ pathWeight I.length P := by
  obtain ⟨Q, hQ, hnd, hlen, hsub, hw⟩ :=
    IsPath.exists_simple I.graph I.source t P hP.1 I.source_valid
  exact ⟨Q, ⟨hQ, fun r => (hw (I.cost r)).trans (hP.2 r)⟩, hnd, hlen, hw I.length⟩

theorem feasible_usable_chain {k : ℕ} (I : MultiInstance k) (t : ℕ) (P : List ℕ)
    (hP : ExactFeasible I t P) (hnd : P.Nodup) :
    P.IsChain (fun u v => (u, v) ∈ usableEdges I) := by
  have hc : P.IsChain (fun u v => ∀ r, I.budget r = 0 → I.cost r u v = 0) := by
    apply chain_forall
    intro r
    by_cases hz : I.budget r = 0
    · have hw : pathWeight (I.cost r) P = 0 :=
        le_antisymm (by simpa [hz] using hP.2 r) (pathWeight_nonneg _ _)
      exact (pathWeight_zero_chain (I.cost r) P hw).imp (fun _ _ he _ => he)
    · exact hP.1.2.2.imp (fun _ _ _ he => (hz he).elim)
  have hn := nodup_chain_ne P hnd
  exact (chain_and _ _ P hP.1.2.2 (chain_and _ _ P hn hc)).imp
    (fun u v he => by simpa [usableEdges] using he)

theorem usable_call_chain {k : ℕ} (A : ClockCall k) (P : List ℕ)
    (hP : P.IsChain (fun u v => (u, v) ∈ usableEdges A.I))
    (hz : A.zeroOnly = true → pathWeight A.I.length P = 0) :
    P.IsChain (fun u v => (u, v) ∈ callEdges A) := by
  cases hb : A.zeroOnly with
  | false => exact hP.imp (fun u v he => by simpa [callEdges, hb] using he)
  | true =>
    have hl := pathWeight_zero_chain A.I.length P (hz hb)
    exact (chain_and _ _ P hP hl).imp (fun u v he => by simpa [callEdges, hb] using he)

theorem feasible_coordinate_bounds {k : ℕ} (A : ClockCall k) (t : ℕ) (P : List ℕ)
    (hP : ExactFeasible A.I t P) (hL : pathWeight A.I.length P ≤ A.L) :
    ∀ r : Fin A.d, pathWeight (coordinateWeight A.I (A.coords.get r)) P ≤
      coordinateBudget A.I A.L (A.coords.get r) := by
  intro r
  by_cases hz : (A.coords.get r).val = 0
  · simpa [coordinateWeight, coordinateBudget, hz] using hL
  · let j : Fin (k - 1) := ⟨(A.coords.get r).val - 1, by have hh := (A.coords.get r).isLt; omega⟩
    simpa [coordinateWeight, coordinateBudget, hz, j] using hP.2 j

theorem accepts_of_exact_feasible {k : ℕ} (A : ClockCall k) (hk : 1 ≤ k)
    (hδ : 0 < A.δ) (hδ1 : A.δ ≤ 1) (hL : 0 < A.L) (P : List ℕ) (t : ℕ)
    (hP : ExactFeasible A.I t P) (hbound : pathWeight A.I.length P ≤ A.L)
    (hz : A.zeroOnly = true → pathWeight A.I.length P = 0) : accepts A t = true := by
  obtain ⟨Q, hQ, hnd, hlen, hw⟩ := feasible_simple A.I t P hP
  have hzQ : A.zeroOnly = true → pathWeight A.I.length Q = 0 := by
    intro hb
    exact le_antisymm (by simpa [hz hb] using hw) (pathWeight_nonneg _ _)
  exact accepts_of_path A hk hδ hδ1 hL Q t hQ.1.1 hQ.1.2.1
    (usable_call_chain A Q (feasible_usable_chain A.I t Q hQ hnd) hzQ)
    (feasible_coordinate_bounds A t Q hQ (hw.trans hbound))

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped NNReal BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem pop_other_vertex {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (v : ℕ) (j : Fin A.d → ℕ) (hv : v ∉ S.queue) :
    (pop A i S).table v j = S.table v j := by
  by_cases hn : S.queue = []
  · simp [pop, hn]
  · rw [pop_of_nonempty A i S hn, relaxAll_table]
    exact put_other _ _ _ _ _ _ (Or.inl (fun h => hv (h.symm ▸ picked_mem A S hn)))

theorem runQueue_other_vertex {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) (v : ℕ) (j : Fin A.d → ℕ) (hv : v ∉ S.queue) :
    (runQueue A i n S).table v j = S.table v j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runQueue_succ]
    have hn : v ∉ (runQueue A i n S).queue :=
      fun hm => hv ((runQueue_queue_sublist A i n S).subset hm)
    exact (pop_other_vertex A i _ v j hn).trans ih

theorem constructTable_other_vertex {k : ℕ} (A : ClockCall k) (v : ℕ)
    (hv : v ∉ incidentVertices A.I) (j : Fin A.d → ℕ) :
    constructTable A v j = ⟨1, .none, 0⟩ := by
  apply fold_preserves (constructLayer A) (fun T => T v j = ⟨1, .none, 0⟩)
    _ _ rfl
  intro i hi T hT
  exact (runQueue_other_vertex A i _ (initializeLayer A T i) v j hv).trans hT

theorem accepts_incident {k : ℕ} (A : ClockCall k) (v : ℕ) (ha : accepts A v = true) :
    v ∈ incidentVertices A.I := by
  classical
  by_contra hv
  have he : value A (constructTable A) v (fun _ => 0) = 1 := by
    unfold value
    split_ifs
    · rfl
    · rw [constructTable_other_vertex A v hv]
  have hh : value A (constructTable A) v (fun _ => 0) ≤ 1 / 4 := by
    simpa only [accepts, decide_eq_true_eq] using ha
  rw [he] at hh
  norm_num at hh

theorem callEdges_graph {k : ℕ} (A : ClockCall k) (u v : ℕ)
    (he : (u, v) ∈ callEdges A) : (u, v) ∈ A.I.graph.edges :=
  List.mem_of_mem_filter (List.mem_of_mem_filter he)

theorem callEdges_zero_budget {k : ℕ} (A : ClockCall k) (u v : ℕ)
    (he : (u, v) ∈ callEdges A) (r : Fin (k - 1)) (hz : A.I.budget r = 0) :
    A.I.cost r u v = 0 := by
  have hu : (u, v) ∈ usableEdges A.I := List.mem_of_mem_filter he
  have hf : u ≠ v ∧ ∀ r, A.I.budget r = 0 → A.I.cost r u v = 0 := by
    simpa using (List.mem_filter.mp hu).2
  exact hf.2 r hz

theorem callEdges_zero_objective {k : ℕ} (A : ClockCall k) (u v : ℕ)
    (he : (u, v) ∈ callEdges A) (hz : A.zeroOnly = true) : A.I.length u v = 0 := by
  simpa [callEdges, hz] using (List.mem_filter.mp he).2

theorem pathWeight_zero_of_chain (w : ℕ → ℕ → ℝ≥0) (P : List ℕ)
    (hP : P.IsChain (fun u v => w u v = 0)) : pathWeight w P = 0 := by
  induction P with
  | nil => simp [pathWeight]
  | cons u P ih =>
    cases P with
    | nil => simp [pathWeight]
    | cons v vs =>
      rw [pathWeight_cons_cons, hP.rel, NNReal.coe_zero, zero_add]
      exact ih hP.tail

theorem potential_original_coordinate {k : ℕ} (A : ClockCall k)
    (hk : 1 ≤ k) (hδ : 0 < A.δ) (hδ1 : A.δ ≤ 1) (hL : 0 < A.L)
    (v : ℕ) (i : Fin A.d → ℕ) (P : List ℕ)
    (hP : multiPotential A (constructTable A) v i P < 1) (r : Fin k)
    (hr : r ∈ clockCoordinates A.I) :
    pathWeight (coordinateWeight A.I r) P ≤ (1 + A.δ) * coordinateBudget A.I A.L r := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
  have hh := potential_coordinate_bound A hk hδ hδ1 hL (constructTable A)
    (constructTable_range A hδ hL) v i P hP j
  simpa only [ClockCall.coords, hj] using hh

theorem retrieve_sound {k : ℕ} (A : ClockCall k) (hk : 1 ≤ k)
    (hδ : 0 < A.δ) (hδ1 : A.δ ≤ 1) (hL : 0 < A.L) (t : ℕ)
    (ha : accepts A t = true) :
    ∃ P : List ℕ, retrieve A t = some P ∧ RelaxedPath A.I A.δ t P ∧
      pathWeight A.I.length P ≤ (1 + A.δ) * A.L ∧
      (A.zeroOnly = true → pathWeight A.I.length P = 0) := by
  obtain ⟨P, i, hret, hhead, hlast, hchain, hP⟩ :=
    retrieve_success A hk hδ hL t (accepts_incident A t ha) ha
  have hgraph : P.IsChain (fun u v => (u, v) ∈ A.I.graph.edges) :=
    hchain.imp (fun u v he => callEdges_graph A u v he)
  have hpath : IsPath A.I.graph A.I.source t P := ⟨hhead, hlast, hgraph⟩
  refine ⟨P, hret, ⟨hpath, ?_⟩, ?_, ?_⟩
  · intro r
    by_cases hz : A.I.budget r = 0
    · have hw : pathWeight (A.I.cost r) P = 0 := pathWeight_zero_of_chain _ P
        (hchain.imp (fun u v he => callEdges_zero_budget A u v he r hz))
      simp [hw, hz]
    · let c : Fin k := ⟨r.val + 1, by have hh := r.isLt; omega⟩
      have hpos : (0 : ℝ) < A.I.budget r := by
        exact_mod_cast (pos_iff_ne_zero.mpr hz)
      have hc : c ∈ clockCoordinates A.I := by
        apply (clockCoordinates_mem A.I c).mpr
        right
        simpa [c, coordinateBudget] using hpos
      have hh := potential_original_coordinate A hk hδ hδ1 hL A.I.source i P hP c hc
      simpa [c, coordinateWeight, coordinateBudget] using hh
  · let c : Fin k := ⟨0, by omega⟩
    have hc : c ∈ clockCoordinates A.I := (clockCoordinates_mem A.I c).mpr (Or.inl rfl)
    have hh := potential_original_coordinate A hk hδ hδ1 hL A.I.source i P hP c hc
    simpa [c, coordinateWeight, coordinateBudget] using hh
  · intro hz
    exact pathWeight_zero_of_chain _ P
      (hchain.imp (fun u v he => callEdges_zero_objective A u v he hz))

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem guessesAux_positive (δ cap : ℝ) (hδ : 0 ≤ δ) (fuel : ℕ)
    (L : ℝ) (hL : 0 < L) (x : ℝ) (hx : x ∈ guessesAux δ cap fuel L) : 0 < x := by
  induction fuel generalizing L with
  | zero => simp [guessesAux] at hx
  | succ fuel ih =>
    simp only [guessesAux, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hL
    · split_ifs at hx with hc
      · simp at hx
      · exact ih (L * (1 + δ)) (mul_pos hL (by linarith)) hx

theorem positiveGuesses_positive {k : ℕ} (I : MultiInstance k) (ε x : ℝ)
    (hε : 0 < ε) (hx : x ∈ positiveGuesses I ε) : 0 < x := by
  unfold positiveGuesses at hx
  split_ifs at hx with h
  · simp at hx
  · exact guessesAux_positive (ε / 4) _ (by linarith) _ _
      (firstPositiveLength_pos (lengthInstance I)) x hx

theorem outerCalls_fields {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε)
    (A : ClockCall k) (hA : A ∈ outerCalls I ε) : A.I = I ∧ A.δ = ε / 4 ∧ 0 < A.L := by
  unfold outerCalls at hA
  split_ifs at hA with h
  · rcases List.mem_cons.mp hA with hA | hA
    · subst A; exact ⟨rfl, rfl, zero_lt_one⟩
    · obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hA
      exact ⟨rfl, rfl, positiveGuesses_positive I ε L hε hL⟩
  · simp at hA

theorem selectedBranch_table_accepts {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (t r : ℕ) (hb : selectedBranch I ε t = .table r) :
    ∃ A, (outerCalls I ε)[r]? = some A ∧ accepts A t = true := by
  unfold selectedBranch at hb
  split at hb
  · cases hb
  · split at hb
    · split at hb
      · cases hb
      · rename_i j hj
        have he : j = r := by simpa using hb
        subst j
        have hp := List.find?_some hj
        cases hA : (outerCalls I ε)[r]? with
        | none => simp [hA] at hp
        | some A => exact ⟨A, rfl, by simpa [hA] using hp⟩
    · split at hb <;> cases hb

theorem selected_table_sound {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (t r : ℕ)
    (hb : selectedBranch I ε t = .table r) :
    ∃ P, selectedPath I ε t = some P ∧ RelaxedPath I ε t P ∧
      ∀ d : ℝ, selectedDistance I ε t = some d → pathWeight I.length P ≤ d := by
  obtain ⟨A, hA, hacc⟩ := selectedBranch_table_accepts I ε t r hb
  have hmem := List.mem_of_getElem? hA
  obtain ⟨hI, hδ, hL⟩ := outerCalls_fields I ε hε A hmem
  have hδ0 : 0 < A.δ := by rw [hδ]; linarith
  have hδ1 : A.δ ≤ 1 := by rw [hδ]; linarith
  obtain ⟨P, hret, hrel, hlen, hzero⟩ := retrieve_sound A hk hδ0 hδ1 hL t hacc
  rw [hI, hδ] at hrel hlen
  rw [hI] at hzero
  refine ⟨P, ?_, ?_, ?_⟩
  · simpa [selectedPath, hb, hA] using hret
  · refine ⟨hrel.1, ?_⟩
    intro j
    exact (hrel.2 j).trans (mul_le_mul_of_nonneg_right (by linarith) (I.budget j).coe_nonneg)
  · intro d hd
    have he : (if A.zeroOnly then 0 else (1 + ε / 4) * A.L) = d := by
      simpa [selectedDistance, hb, hA] using hd
    rw [← he]
    cases hz : A.zeroOnly with
    | false => simpa [hz] using hlen
    | true => simpa [hz, hzero hz]

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem guessesAux_ge (δ cap : ℝ) (hδ : 0 ≤ δ) (fuel : ℕ)
    (L : ℝ) (hL : 0 ≤ L) (x : ℝ) (hx : x ∈ guessesAux δ cap fuel L) : L ≤ x := by
  induction fuel generalizing L with
  | zero => simp [guessesAux] at hx
  | succ fuel ih =>
    simp only [guessesAux, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · split_ifs at hx with hc
      · simp at hx
      · have hstep : L ≤ L * (1 + δ) := by nlinarith [mul_nonneg hL hδ]
        exact hstep.trans (ih _ (hL.trans hstep) hx)

theorem guessesAux_ordered (δ cap : ℝ) (hδ : 0 ≤ δ) (fuel : ℕ)
    (L : ℝ) (hL : 0 ≤ L) : (guessesAux δ cap fuel L).Pairwise (· ≤ ·) := by
  induction fuel generalizing L with
  | zero => simp [guessesAux]
  | succ fuel ih =>
    rw [guessesAux]
    split_ifs with hc
    · simp
    · have hstep : L ≤ L * (1 + δ) := by nlinarith [mul_nonneg hL hδ]
      refine List.pairwise_cons.mpr ⟨?_, ih _ (hL.trans hstep)⟩
      intro x hx
      exact hstep.trans (guessesAux_ge δ cap hδ fuel _ (hL.trans hstep) x hx)

theorem guessesAux_cover (δ cap : ℝ) (hδ : 0 < δ) (fuel : ℕ)
    (L x : ℝ) (hL : 0 < L) (hseed : L ≤ (1 + δ) * x) (hx : x ≤ cap)
    (hreach : cap ≤ L * (1 + δ) ^ fuel) :
    ∃ y ∈ guessesAux δ cap (fuel + 1) L, x ≤ y ∧ y ≤ (1 + δ) * x := by
  induction fuel generalizing L with
  | zero =>
    have hxL : x ≤ L := by simpa using hx.trans hreach
    exact ⟨L, by simp [guessesAux], hxL, hseed⟩
  | succ fuel ih =>
    by_cases hxL : x ≤ L
    · exact ⟨L, by simp [guessesAux], hxL, hseed⟩
    · have hLc : ¬cap ≤ L := by linarith
      have hnext : 0 < L * (1 + δ) := mul_pos hL (by linarith)
      have hseed' : L * (1 + δ) ≤ (1 + δ) * x := by nlinarith
      have hreach' : cap ≤ (L * (1 + δ)) * (1 + δ) ^ fuel := by
        simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hreach
      obtain ⟨y, hy, hxy, hyx⟩ := ih _ hnext hseed' hreach'
      refine ⟨y, ?_, hxy, hyx⟩
      rw [guessesAux, if_neg hLc]
      exact List.mem_cons_of_mem L hy

theorem log_ceiling_reaches (a r cap : ℝ) (ha : 0 < a) (hr : 1 < r) (hc : 0 < cap) :
    cap ≤ a * r ^ Nat.ceil (Real.log (cap / a) / Real.log r) := by
  have hr0 : 0 < r := by linarith
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hn : Real.log (cap / a) ≤
      (Nat.ceil (Real.log (cap / a) / Real.log r) : ℝ) * Real.log r :=
    (div_le_iff₀ hlog).mp (Nat.le_ceil _)
  have he := Real.exp_le_exp.mpr hn
  rw [Real.exp_log (div_pos hc ha), Real.exp_nat_mul, Real.exp_log hr0] at he
  have hh := (div_le_iff₀ ha).mp he
  simpa only [mul_comm] using hh

theorem positiveGuesses_ordered {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) :
    (positiveGuesses I ε).Pairwise (· ≤ ·) := by
  unfold positiveGuesses
  split_ifs
  · simp
  · exact guessesAux_ordered _ _ (by linarith) _ _ (firstPositiveLength_pos _).le

theorem positiveGuesses_cover {k : ℕ} (I : MultiInstance k) (ε x : ℝ) (hε : 0 < ε)
    (hne : positiveLengths (lengthInstance I) ≠ [])
    (hlo : firstPositiveLength (lengthInstance I) ≤ x)
    (hhi : x ≤ (I.graph.n : ℝ) * largestLength (lengthInstance I)) :
    ∃ L ∈ positiveGuesses I ε, x ≤ L ∧ L ≤ (1 + ε / 4) * x := by
  let a := firstPositiveLength (lengthInstance I)
  let cap := (I.graph.n : ℝ) * largestLength (lengthInstance I)
  let r := 1 + ε / 4
  let n := Nat.ceil (Real.log (cap / a) / Real.log r)
  have ha : 0 < a := firstPositiveLength_pos _
  have hx : 0 < x := ha.trans_le hlo
  have hc : 0 < cap := hx.trans_le hhi
  have hr : 1 < r := by dsimp [r]; linarith
  have hreach : cap ≤ a * r ^ n := log_ceiling_reaches a r cap ha hr hc
  have hstep : a * r ^ n ≤ a * r ^ (n + 1) := by
    rw [pow_succ]
    have hn : 0 ≤ a * r ^ n := by positivity
    nlinarith
  have hseed : a ≤ r * x := by nlinarith
  have hh := guessesAux_cover (ε / 4) cap (by linarith) (n + 1) a x ha hseed hhi
    (hreach.trans hstep)
  have hg : ¬((positiveLengths (lengthInstance I)).isEmpty ∨ ε ≤ 0) := by
    simpa only [List.isEmpty_iff, not_or, not_le] using And.intro hne hε
  simpa only [positiveGuesses, if_neg hg, a, cap, r, n, Nat.add_assoc] using hh

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped NNReal

namespace NearLinearRSP.TwoResources.Supplement

theorem positive_path_edge (G : Digraph) (w : ℕ → ℕ → ℝ≥0) (P : List ℕ)
    (hP : P.IsChain (fun u v => (u, v) ∈ G.edges)) (hp : 0 < pathWeight w P) :
    ∃ u v, (u, v) ∈ G.edges ∧ 0 < (w u v : ℝ) ∧ (w u v : ℝ) ≤ pathWeight w P := by
  induction P with
  | nil => simp [pathWeight] at hp
  | cons u P ih =>
    cases P with
    | nil => simp [pathWeight] at hp
    | cons v vs =>
      by_cases hw : 0 < (w u v : ℝ)
      · refine ⟨u, v, hP.rel, hw, ?_⟩
        rw [pathWeight_cons_cons]
        have hn := pathWeight_nonneg w (v :: vs)
        linarith
      · have hw0 : (w u v : ℝ) = 0 := le_antisymm (not_lt.mp hw) (w u v).coe_nonneg
        have htail : pathWeight w (u :: v :: vs) = pathWeight w (v :: vs) := by
          rw [pathWeight_cons_cons, hw0, zero_add]
        rw [htail] at hp ⊢
        exact ih hP.tail hp

theorem positive_edge_member {k : ℕ} (I : MultiInstance k) (u v : ℕ)
    (he : (u, v) ∈ I.graph.edges) (hp : 0 < (I.length u v : ℝ)) :
    (I.length u v : ℝ) ∈ positiveLengths (lengthInstance I) := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_map.mpr ⟨(u, v), he, rfl⟩, by simpa using hp⟩

theorem edge_length_le_largest {k : ℕ} (I : MultiInstance k) (u v : ℕ)
    (he : (u, v) ∈ I.graph.edges) : (I.length u v : ℝ) ≤ largestLength (lengthInstance I) := by
  by_cases hp : 0 < (I.length u v : ℝ)
  · exact member_le_largestLength _ _ (positive_edge_member I u v he hp)
  · exact (not_lt.mp hp).trans (largestLength_nonneg _)

theorem positive_path_bounds {k : ℕ} (I : MultiInstance k) (P : List ℕ) (t : ℕ)
    (hP : IsPath I.graph I.source t P) (hnd : P.Nodup) (hp : 0 < pathWeight I.length P) :
    positiveLengths (lengthInstance I) ≠ [] ∧
      firstPositiveLength (lengthInstance I) ≤ pathWeight I.length P ∧
      pathWeight I.length P ≤ (I.graph.n : ℝ) * largestLength (lengthInstance I) := by
  obtain ⟨u, v, he, hw, hb⟩ := positive_path_edge I.graph I.length P hP.2.2 hp
  have hm := positive_edge_member I u v he hw
  exact ⟨List.ne_nil_of_mem hm, (firstPositiveLength_le_member _ _ hm).trans hb,
    IsPath.weight_le_n_mul I.graph I.source t P hP I.source_valid hnd I.length
      (largestLength (lengthInstance I)) (largestLength_nonneg _) (edge_length_le_largest I)⟩

noncomputable def callReported {k : ℕ} (ε : ℝ) (A : ClockCall k) : ℝ :=
  if A.zeroOnly then 0 else (1 + ε / 4) * A.L

theorem outerCalls_ordered {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) :
    (outerCalls I ε).Pairwise (fun A B => callReported ε A ≤ callReported ε B) := by
  unfold outerCalls
  split_ifs
  · apply List.pairwise_cons.mpr
    constructor
    · intro A hA
      obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hA
      have hp := positiveGuesses_positive I ε L hε hL
      dsimp [callReported]
      positivity
    · apply List.pairwise_map.mpr
      exact (positiveGuesses_ordered I ε hε).imp (fun {x y} hxy =>
        by simpa only [callReported, Bool.false_eq_true, if_false] using
          mul_le_mul_of_nonneg_left hxy (by linarith : 0 ≤ 1 + ε / 4))
  · simp

theorem outer_accepting_approximation {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hb : hasPositiveBudget I = true)
    (R : List ℕ) (t : ℕ) (hR : ExactFeasible I t R) :
    ∃ A ∈ outerCalls I ε, accepts A t = true ∧
      callReported ε A ≤ (1 + ε) * pathWeight I.length R := by
  obtain ⟨Q, hQ, hnd, hlen, hw⟩ := feasible_simple I t R hR
  by_cases hz : pathWeight I.length Q = 0
  · let A : ClockCall k := ⟨I, ε / 4, 1, true⟩
    refine ⟨A, by simp [outerCalls, hb, A], ?_, ?_⟩
    · exact accepts_of_exact_feasible A hk (by dsimp [A]; linarith)
        (by dsimp [A]; linarith) zero_lt_one Q t hQ (by simpa [A, hz]) (fun _ => hz)
    · dsimp [callReported, A]
      exact mul_nonneg (by linarith) (pathWeight_nonneg _ _)
  · have hqpos : 0 < pathWeight I.length Q := lt_of_le_of_ne (pathWeight_nonneg _ _) (Ne.symm hz)
    obtain ⟨hne, hlo, hhi⟩ := positive_path_bounds I Q t hQ.1 hnd hqpos
    obtain ⟨L, hL, hQL, hLQ⟩ := positiveGuesses_cover I ε (pathWeight I.length Q) hε hne hlo hhi
    let A : ClockCall k := ⟨I, ε / 4, L, false⟩
    refine ⟨A, ?_, ?_, ?_⟩
    · simp only [outerCalls, hb, if_true, List.mem_cons, List.mem_map]
      exact Or.inr ⟨L, hL, rfl⟩
    · exact accepts_of_exact_feasible A hk (by dsimp [A]; linarith)
        (by dsimp [A]; linarith) (positiveGuesses_positive I ε L hε hL) Q t hQ hQL
        (by simp [A])
    · have hf : (1 + ε / 4) ^ 2 ≤ 1 + ε := by nlinarith
      calc
        callReported ε A = (1 + ε / 4) * L := rfl
        _ ≤ (1 + ε / 4) * ((1 + ε / 4) * pathWeight I.length Q) :=
          mul_le_mul_of_nonneg_left hLQ (by linarith)
        _ = (1 + ε / 4) ^ 2 * pathWeight I.length Q := by ring
        _ ≤ (1 + ε) * pathWeight I.length Q :=
          mul_le_mul_of_nonneg_right hf hqpos.le
        _ ≤ (1 + ε) * pathWeight I.length R := mul_le_mul_of_nonneg_left hw (by linarith)

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem find_range_le (p : ℕ → Bool) (n j : ℕ)
    (hf : (List.range n).find? p = some j) (r : ℕ) (hr : r < n) (hp : p r = true) :
    j ≤ r := by
  obtain ⟨_, i, hi, he, hprev⟩ := List.find?_eq_some_iff_getElem.mp hf
  have hij : i = j := by simpa using he
  by_contra hn
  have hri : r < i := by omega
  have hh := hprev r hri
  simpa [hp] using hh

theorem find_range_exists (p : ℕ → Bool) (n r : ℕ) (hr : r < n) (hp : p r = true) :
    ∃ j, (List.range n).find? p = some j := by
  cases hf : (List.range n).find? p with
  | none => exact ((List.find?_eq_none.mp hf) r (List.mem_range.mpr hr) hp).elim
  | some j => exact ⟨j, rfl⟩

theorem outer_select_of_accepting {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (ht : t ≠ I.source) (hb : hasPositiveBudget I = true)
    (A : ClockCall k) (hA : A ∈ outerCalls I ε) (ha : accepts A t = true) :
    ∃ r B, selectedBranch I ε t = .table r ∧ (outerCalls I ε)[r]? = some B ∧
      callReported ε B ≤ callReported ε A := by
  classical
  let calls := outerCalls I ε
  let p : ℕ → Bool := fun r => match calls[r]? with
    | none => false
    | some B => accepts B t
  obtain ⟨i, hi, hiA⟩ := List.mem_iff_getElem.mp hA
  have hpi : p i = true := by simp only [p, calls, List.getElem?_eq_getElem hi, hiA, ha]
  obtain ⟨j, hj⟩ := find_range_exists p calls.length i hi hpi
  have hji := find_range_le p calls.length j hj i hi hpi
  have hjlen : j < calls.length := List.mem_range.mp (List.mem_of_find?_eq_some hj)
  let B := calls[j]
  refine ⟨j, B, ?_, List.getElem?_eq_getElem hjlen, ?_⟩
  · simp only [selectedBranch, if_neg ht, hb, if_true]
    change (match (List.range calls.length).find? p with
      | none => OutputBranch.absent
      | some r => OutputBranch.table r) = .table j
    rw [hj]
  · rcases Nat.lt_or_eq_of_le hji with hlt | heq
    · have ho := (List.pairwise_iff_getElem.mp (outerCalls_ordered I ε hε)) j i hjlen hi hlt
      simpa only [hiA] using ho
    · subst j
      simpa only [B, calls, hiA] using le_refl (callReported ε A)

theorem selected_table_completeness {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (t : ℕ) (ht : t ≠ I.source)
    (hb : hasPositiveBudget I = true) (R : List ℕ) (hR : ExactFeasible I t R) :
    ∃ d, selectedDistance I ε t = some d ∧ d ≤ (1 + ε) * pathWeight I.length R := by
  obtain ⟨A, hA, ha, hbound⟩ := outer_accepting_approximation I hk ε hε hε1 hb R t hR
  obtain ⟨r, B, hbranch, hB, hBA⟩ := outer_select_of_accepting I ε hε t ht hb A hA ha
  exact ⟨callReported ε B, by simp [selectedDistance, hbranch, hB, callReported], hBA.trans hbound⟩

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement

noncomputable def budgetAllow {k : ℕ} (I : MultiInstance k) (u v : ℕ) : Bool :=
  decide (∀ r, I.budget r = 0 → I.cost r u v = 0)

abbrev EdgeAllowed {k : ℕ} (I : MultiInstance k) (e : ℕ × ℕ) : Prop :=
  e.1 ≠ e.2 ∧ ∀ r, I.budget r = 0 → I.cost r e.1 e.2 = 0

def ShortestMatches (S : TreeQueue) (U : ShortestState) : Prop :=
  S.queue = U.queue ∧ ∀ v,
    (S.tree v).distance = (U.cells v).distance ∧ (S.tree v).parent = (U.cells v).parent

theorem distanceLess_bridge (x y : Option ℝ) :
    NearLinearRSP.TwoResources.distanceLess x y = distanceLess x y := by
  cases x <;> cases y <;> rfl

theorem shortestMatches_update (S : TreeQueue) (U : ShortestState)
    (h : ShortestMatches S U) (v : ℕ) (d : Option ℝ) (p : Option ℕ) (r : ℕ) :
    ShortestMatches { S with tree := Function.update S.tree v ⟨d, p, r⟩ }
      { U with cells := Function.update U.cells v ⟨d, p⟩ } := by
  refine ⟨h.1, ?_⟩
  intro w
  by_cases hw : w = v
  · subst w; simp
  · simpa [Function.update_of_ne hw] using h.2 w

theorem treeRelax_matches {k : ℕ} (I : MultiInstance k) (u : ℕ)
    (S : TreeQueue) (U : ShortestState) (h : ShortestMatches S U)
    (e : ℕ × ℕ) (he : EdgeAllowed I e) :
    ShortestMatches (treeRelax (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) u S e)
      (relaxShortest I u U e) := by
  classical
  rcases he with ⟨hne, hz⟩
  have ha : budgetAllow I e.1 e.2 = true := by simpa only [budgetAllow, decide_eq_true_eq] using hz
  have hg : (e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue ∧ budgetAllow I e.1 e.2 = true) ↔
      (e.1 = u ∧ e.2 ∈ U.queue) := by
    constructor
    · intro hh; exact ⟨hh.1, h.1 ▸ hh.2.2.1⟩
    · intro hh; exact ⟨hh.1, hne, h.1.symm ▸ hh.2, ha⟩
  unfold treeRelax relaxShortest
  dsimp only
  rw [if_congr hg rfl rfl]
  split_ifs with hc
  · rw [(h.2 u).1]
    cases hd : (U.cells u).distance with
    | none => exact h
    | some d =>
      dsimp only
      rw [distanceLess_bridge, (h.2 e.2).1]
      split_ifs
      · exact shortestMatches_update S U h e.2 _ _ 0
      · exact h
  · exact h

theorem treeRelax_rejected {k : ℕ} (I : MultiInstance k) (u : ℕ)
    (S : TreeQueue) (e : ℕ × ℕ) (he : ¬EdgeAllowed I e) :
    treeRelax (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) u S e = S := by
  unfold treeRelax
  rw [if_neg]
  intro h
  apply he
  exact ⟨h.2.1, by simpa only [budgetAllow, decide_eq_true_eq] using h.2.2.2⟩

theorem treeRelaxFold_matches {k : ℕ} (I : MultiInstance k) (u : ℕ)
    (es : List (ℕ × ℕ)) (S : TreeQueue) (U : ShortestState) (h : ShortestMatches S U) :
    ShortestMatches
      (es.foldl (treeRelax (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) u) S)
      ((es.filter (fun e => decide (EdgeAllowed I e))).foldl (relaxShortest I u) U) := by
  classical
  induction es generalizing S U with
  | nil => exact h
  | cons e es ih =>
    by_cases he : EdgeAllowed I e
    · have hb : decide (EdgeAllowed I e) = true := by simpa only [decide_eq_true_eq] using he
      rw [List.filter_cons, if_pos hb, List.foldl_cons, List.foldl_cons]
      exact ih _ _ (treeRelax_matches I u S U h e he)
    · have hb : ¬decide (EdgeAllowed I e) = true := by simpa only [decide_eq_true_eq] using he
      rw [List.filter_cons, if_neg hb, List.foldl_cons, treeRelax_rejected I u S e he]
      exact ih S U h

theorem treeSettle_matches (S : TreeQueue) (U : ShortestState)
    (h : ShortestMatches S U) (u : ℕ) :
    ShortestMatches (treeSettle S u) { U with queue := U.queue.erase u } := by
  refine ⟨congrArg (fun q => q.erase u) h.1, ?_⟩
  intro v
  by_cases hv : v = u
  · subst v
    simpa [treeSettle] using h.2 u
  · simpa [treeSettle, Function.update_of_ne hv] using h.2 v

theorem treePop_matches {k : ℕ} (I : MultiInstance k)
    (S : TreeQueue) (U : ShortestState) (h : ShortestMatches S U) :
    ShortestMatches (treePop (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) S)
      (popShortest I U) := by
  have hf : (fun x y => if NearLinearRSP.TwoResources.distanceLess
      (S.tree y).distance (S.tree x).distance then y else x) =
      (fun x y => if distanceLess (U.cells y).distance (U.cells x).distance then y else x) := by
    funext x y
    rw [distanceLess_bridge, (h.2 y).1, (h.2 x).1]
  unfold treePop popShortest
  rw [h.1]
  cases hq : U.queue with
  | nil => exact h
  | cons v vs =>
    dsimp only
    rw [hf]
    let u := (v :: vs).foldl
      (fun x y => if distanceLess (U.cells y).distance (U.cells x).distance then y else x) v
    have hm := treeRelaxFold_matches I u I.graph.edges _ _ (treeSettle_matches S U h u)
    simpa only [treeSettle, h.1, hq, usableEdges, EdgeAllowed, lengthInstance, u] using hm

theorem treeRun_matches {k : ℕ} (I : MultiInstance k) (n : ℕ)
    (S : TreeQueue) (U : ShortestState) (h : ShortestMatches S U) :
    ShortestMatches (treeRun (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) n S)
      ((List.range n).foldl (fun U _ => popShortest I U) U) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [treeRun_succ, List.range_succ, List.foldl_append]
    exact treePop_matches I _ _ ih

noncomputable def rankedShortest {k : ℕ} (I : MultiInstance k) : ShortestTree :=
  NearLinearRSP.TwoResources.shortestTree (lengthInstance I) (budgetAllow I) (fun u v => I.length u v)

theorem shortestTree_bridge {k : ℕ} (I : MultiInstance k) (v : ℕ) :
    (rankedShortest I v).distance = (shortestTree I v).distance ∧
      (rankedShortest I v).parent = (shortestTree I v).parent := by
  have hinit : ShortestMatches (treeInitial (lengthInstance I))
      ⟨fun v => ⟨if v = I.source then some 0 else none, none⟩, incidentVertices I⟩ := by
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  exact (treeRun_matches I (incidentVertices I).length _ _ hinit).2 v

theorem shortestTree_rank_bound {k : ℕ} (I : MultiInstance k) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I v).distance = some d) :
    (rankedShortest I v).rank < (incidentVertices I).length := by
  apply shortestTree_finite_rank (lengthInstance I) (budgetAllow I) _ v d
  exact (shortestTree_bridge I v).1.trans hd

theorem shortestTree_parent {k : ℕ} (I : MultiInstance k) (v : ℕ) (d : ℝ)
    (hv : v ≠ I.source) (hd : (shortestTree I v).distance = some d) :
    ∃ u a, (shortestTree I v).parent = some u ∧ (shortestTree I u).distance = some a ∧
      d = a + (I.length u v : ℝ) ∧ (u, v) ∈ I.graph.edges ∧ budgetAllow I u v = true ∧
      (rankedShortest I u).rank < (rankedShortest I v).rank := by
  obtain ⟨u, a, hp, ha, he, hg, hal, hr⟩ := shortestTree_finite_parent
    (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) v d hv
    ((shortestTree_bridge I v).1.trans hd)
  exact ⟨u, a, ((shortestTree_bridge I v).2.symm.trans hp),
    ((shortestTree_bridge I u).1.symm.trans ha), he, hg, hal, hr⟩

theorem shortestTree_source_distance {k : ℕ} (I : MultiInstance k) :
    (shortestTree I I.source).distance = some 0 := by
  rw [← (shortestTree_bridge I I.source).1]
  exact shortestTree_source_zero (lengthInstance I) (budgetAllow I)
    (fun u v => I.length u v) (fun u v => (I.length u v).coe_nonneg)

theorem shortestTree_feasible_bound {k : ℕ} (I : MultiInstance k) (P : List ℕ) (t : ℕ)
    (hP : ExactFeasible I t P) :
    ∃ d, (shortestTree I t).distance = some d ∧ d ≤ pathWeight I.length P := by
  obtain ⟨Q, hQ, hnd, hlen, hw⟩ := feasible_simple I t P hP
  have hallow : Q.IsChain (fun u v => budgetAllow I u v = true) :=
    (feasible_usable_chain I t Q hQ hnd).imp (fun u v he => by
      have hh : u ≠ v ∧ ∀ r, I.budget r = 0 → I.cost r u v = 0 := by
        simpa using (List.mem_filter.mp he).2
      simpa only [budgetAllow, decide_eq_true_eq] using hh.2)
  obtain ⟨d, hd, hb⟩ := shortestTree_path_bound (lengthInstance I) (budgetAllow I) I.length
    Q t hQ.1 hallow
  exact ⟨d, (shortestTree_bridge I t).1.symm.trans hd, hb.trans hw⟩

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem isPath_append_vertex (G : Digraph) (s u v : ℕ) (P : List ℕ)
    (hP : IsPath G s u P) (he : (u, v) ∈ G.edges) : IsPath G s v (P ++ [v]) := by
  refine ⟨?_, by simp, ?_⟩
  · simpa only [List.head?_append, hP.1, Option.some_or] using hP.1
  · apply List.isChain_append.mpr
    refine ⟨hP.2.2, by simp, ?_⟩
    intro x hx y hy
    have hx' : u = x := by simpa only [hP.2.1, Option.mem_some_iff] using hx
    have hy' : v = y := by simpa using hy
    simpa only [← hx', ← hy'] using he

theorem followParents_sound {k : ℕ} (I : MultiInstance k) (fuel v : ℕ) (d : ℝ)
    (hd : (shortestTree I v).distance = some d)
    (hr : (rankedShortest I v).rank < fuel) :
    ∃ P, followParents I.source (shortestTree I) fuel v = some P ∧
      IsPath I.graph I.source v P ∧ pathWeight I.length P = d ∧
      ∀ r, I.budget r = 0 → pathWeight (I.cost r) P = 0 := by
  induction fuel generalizing v d with
  | zero => omega
  | succ fuel ih =>
    by_cases hv : v = I.source
    · subst v
      have hd0 : d = 0 := by
        rw [shortestTree_source_distance I] at hd
        exact (Option.some.inj hd).symm
      refine ⟨[I.source], by simp [followParents], ?_, ?_, ?_⟩
      · simp [IsPath]
      · simp [pathWeight, hd0]
      · intro r _; simp [pathWeight]
    · obtain ⟨u, a, hp, ha, he, hg, hal, hru⟩ := shortestTree_parent I v d hv hd
      obtain ⟨P, hfollow, hP, hlen, hcost⟩ := ih u a ha (by omega)
      refine ⟨P ++ [v], ?_, isPath_append_vertex I.graph I.source u v P hP hg, ?_, ?_⟩
      · simp only [followParents, if_neg hv, hp, hfollow, Option.map_some]
      · rw [pathWeight_append_singleton _ P u v hP.2.1, hlen, ← he]
      · intro r hz
        have hedge : I.cost r u v = 0 :=
          (of_decide_eq_true hal : ∀ r, I.budget r = 0 → I.cost r u v = 0) r hz
        rw [pathWeight_append_singleton _ P u v hP.2.1, hcost r hz, hedge]
        simp

theorem shortestPath_sound {k : ℕ} (I : MultiInstance k) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I v).distance = some d) :
    ∃ P, shortestPath I v = some P ∧ IsPath I.graph I.source v P ∧
      pathWeight I.length P = d ∧ ∀ r, I.budget r = 0 → pathWeight (I.cost r) P = 0 := by
  have hr := shortestTree_rank_bound I v d hd
  obtain ⟨P, hp, hP, hl, hc⟩ := followParents_sound I ((incidentVertices I).length + 1) v d hd
    (by omega)
  exact ⟨P, by simpa [shortestPath, hd] using hp, hP, hl, hc⟩

theorem budgets_zero {k : ℕ} (I : MultiInstance k) (h : hasPositiveBudget I = false)
    (r : Fin (k - 1)) : I.budget r = 0 := by
  have hn : ¬∃ r, 0 < I.budget r := by simpa only [hasPositiveBudget, decide_eq_false_iff_not] using h
  exact le_antisymm (not_lt.mp (fun hr => hn ⟨r, hr⟩)) (by positivity)

theorem selectedBranch_ordinary_fields {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ)
    (hb : selectedBranch I ε t = .ordinary) :
    hasPositiveBudget I = false ∧ ∃ d, (shortestTree I t).distance = some d := by
  unfold selectedBranch at hb
  split at hb
  · cases hb
  · split at hb
    · split at hb <;> cases hb
    · rename_i hn
      split at hb
      · rename_i hd
        exact ⟨Bool.eq_false_iff.mpr hn, Option.isSome_iff_exists.mp hd⟩
      · cases hb

theorem selected_ordinary_sound {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ)
    (hb : selectedBranch I ε t = .ordinary) :
    ∃ P d, selectedPath I ε t = some P ∧ selectedDistance I ε t = some d ∧
      RelaxedPath I ε t P ∧ pathWeight I.length P = d ∧
      ∀ R, ExactFeasible I t R → d ≤ pathWeight I.length R := by
  obtain ⟨hz, d, hd⟩ := selectedBranch_ordinary_fields I ε t hb
  obtain ⟨P, hP, hp, hl, hc⟩ := shortestPath_sound I t d hd
  refine ⟨P, d, ?_, ?_, ⟨hp, ?_⟩, hl, ?_⟩
  · simpa [selectedPath, hb] using hP
  · simpa [selectedDistance, hb] using hd
  · intro r
    rw [hc r (budgets_zero I hz r), budgets_zero I hz r]
    simp
  · intro R hR
    obtain ⟨a, ha, hbound⟩ := shortestTree_feasible_bound I R t hR
    have he : a = d := Option.some.inj (ha.symm.trans hd)
    simpa only [he] using hbound

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem selectedBranch_source_only {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ)
    (hb : selectedBranch I ε t = .source) : t = I.source := by
  by_cases ht : t = I.source
  · exact ht
  · simp only [selectedBranch, if_neg ht] at hb
    split at hb
    · split at hb <;> cases hb
    · split at hb <;> cases hb

theorem selected_feasible_bound {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (t : ℕ) (R : List ℕ)
    (hR : ExactFeasible I t R) :
    ∃ d, selectedDistance I ε t = some d ∧ d ≤ (1 + ε) * pathWeight I.length R := by
  by_cases ht : t = I.source
  · subst t
    exact ⟨0, selectedDistance_source I ε, mul_nonneg (by linarith) (pathWeight_nonneg _ _)⟩
  · cases hb : hasPositiveBudget I with
    | true => exact selected_table_completeness I hk ε hε hε1 t ht hb R hR
    | false =>
      obtain ⟨d, hd, hbound⟩ := shortestTree_feasible_bound I R t hR
      refine ⟨d, by simp [selectedDistance, selectedBranch, ht, hb, hd], hbound.trans ?_⟩
      have hw := pathWeight_nonneg I.length R
      have hm := mul_nonneg hε.le hw
      nlinarith

theorem selected_distance_sound {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (t : ℕ) (d : ℝ)
    (hd : selectedDistance I ε t = some d) :
    ∃ P, selectedPath I ε t = some P ∧ RelaxedPath I ε t P ∧ pathWeight I.length P ≤ d := by
  cases hb : selectedBranch I ε t with
  | absent => simp [selectedDistance, hb] at hd
  | source =>
    have ht := selectedBranch_source_only I ε t hb
    subst t
    have hd0 : d = 0 := by simpa [selectedDistance_source] using hd.symm
    exact ⟨[I.source], selectedPath_source I ε, source_relaxed I ε hε.le,
      by simp [pathWeight, hd0]⟩
  | ordinary =>
    obtain ⟨P, a, hP, ha, hrel, hlen, _⟩ := selected_ordinary_sound I ε t hb
    have he : a = d := Option.some.inj (ha.symm.trans hd)
    exact ⟨P, hP, hrel, by rw [hlen, he]⟩
  | table r =>
    obtain ⟨P, hP, hrel, hlen⟩ := selected_table_sound I hk ε hε hε1 t r hb
    exact ⟨P, hP, hrel, hlen d hd⟩

theorem selected_path_sound {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (t : ℕ) (P : List ℕ)
    (hP : selectedPath I ε t = some P) : RelaxedPath I ε t P := by
  cases hd : selectedDistance I ε t with
  | none =>
    have hb := (selectedDistance_none_iff I ε t).mp hd
    simp [selectedPath, hb] at hP
  | some d =>
    obtain ⟨Q, hQ, hrel, _⟩ := selected_distance_sound I hk ε hε hε1 t d hd
    have he : Q = P := Option.some.inj (hQ.symm.trans hP)
    exact he ▸ hrel

theorem selected_semantics_correct {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (t : ℕ) :
    (∀ d : ℝ, selectedDistance I ε t = some d →
      ∃ P : List ℕ, selectedPath I ε t = some P ∧ RelaxedPath I ε t P ∧
        pathWeight I.length P ≤ d ∧
        ∀ R : List ℕ, ExactFeasible I t R → d ≤ (1 + ε) * pathWeight I.length R) ∧
    ((∃ R : List ℕ, ExactFeasible I t R) → (selectedDistance I ε t).isSome = true) ∧
    (∀ P : List ℕ, selectedPath I ε t = some P → RelaxedPath I ε t P) := by
  refine ⟨?_, ?_, selected_path_sound I hk ε hε hε1 t⟩
  · intro d hd
    obtain ⟨P, hP, hrel, hlen⟩ := selected_distance_sound I hk ε hε hε1 t d hd
    refine ⟨P, hP, hrel, hlen, ?_⟩
    intro R hR
    obtain ⟨a, ha, hbound⟩ := selected_feasible_bound I hk ε hε hε1 t R hR
    have he : a = d := Option.some.inj (ha.symm.trans hd)
    simpa only [he] using hbound
  · rintro ⟨R, hR⟩
    obtain ⟨d, hd, _⟩ := selected_feasible_bound I hk ε hε hε1 t R hR
    simp [hd]

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement.ParentQuery

theorem incident_length_le_n {k : ℕ} (I : MultiInstance k) :
    (incidentVertices I).length ≤ I.graph.n := by
  have hnd : (incidentVertices I).Nodup := activeVertices_nodup (lengthInstance I)
  have hsub : incidentVertices I ⊆ List.range I.graph.n :=
    fun v hv => List.mem_range.mpr (incident_valid I v hv)
  simpa using hnd.length_le_of_subset hsub

theorem followParents_walk {k : ℕ} (I : MultiInstance k) (next : ℕ → ℕ)
    (hm : ∀ v ∈ incidentVertices I, next v = ((shortestTree I v).parent.map (· + 1)).getD 0)
    (fuel v : ℕ) (d : ℝ) (hd : (shortestTree I v).distance = some d)
    (hr : (rankedShortest I v).rank < fuel) :
    ∃ P, followParents I.source (shortestTree I) fuel v = some P ∧
      Walk I.graph.n I.source next v P ∧ P.length ≤ fuel := by
  induction fuel generalizing v d with
  | zero => omega
  | succ fuel ih =>
    by_cases hv : v = I.source
    · subst v
      exact ⟨[I.source], by simp [followParents], .sourcePath, by simp⟩
    · obtain ⟨u, a, hp, ha, _, hg, _, hru⟩ := shortestTree_parent I v d hv hd
      obtain ⟨P, hP, hw, hlen⟩ := ih u a ha (by omega)
      have hinc : v ∈ incidentVertices I := activeVertices_edge_right (lengthInstance I) u v hg
      have hparent : next v = u + 1 := by simp [hm v hinc, hp]
      exact ⟨P ++ [v], by simp only [followParents, if_neg hv, hp, hP, Option.map_some],
        .edge (I.graph.endpoints _ hg).2 hv hparent hw, by simp; omega⟩

theorem ordinary_walk {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ)
    (S : RAMState) (henc : EncodesMultiOutput I ε S)
    (ht : selectedBranch I ε t = .ordinary) :
    ∃ P, selectedPath I ε t = some P ∧
      Walk I.graph.n I.source (fun v => S.nm (targetSlot k v + 2)) t P ∧ P.length ≤ I.graph.n + 1 := by
  obtain ⟨hz, d, hd⟩ := selectedBranch_ordinary_fields I ε t ht
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hm, _⟩ := henc
  have hr := shortestTree_rank_bound I t d hd
  obtain ⟨P, hfollow, hw, hlen⟩ := followParents_walk I _ (hm hz)
    ((incidentVertices I).length + 1) t d hd (by omega)
  exact ⟨P, by simpa [selectedPath, ht, shortestPath, hd] using hfollow, hw,
    hlen.trans (Nat.add_le_add_right (incident_length_le_n I) 1)⟩

theorem source_walk {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ)
    (S : RAMState) (ht : selectedBranch I ε t = .source) :
    ∃ P, selectedPath I ε t = some P ∧
      Walk I.graph.n I.source (fun v => S.nm (targetSlot k v + 2)) t P ∧ P.length ≤ I.graph.n + 1 := by
  obtain rfl := selectedBranch_source_only I ε t ht
  exact ⟨[I.source], selectedPath_source I ε, .sourcePath, by simp⟩

end NearLinearRSP.TwoResources.Supplement.ParentQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def selectDimension (f : ℕ → Cmd) : ℕ → Cmd
  | 0 => .seq (.atom ⟨.natConst 69 0, trivial⟩) (f 0)
  | n + 1 => .seq (.atom ⟨.natConst 69 (n + 1), trivial⟩)
      (.branch (.nat .eq 68 69) (f (n + 1)) (selectDimension f n))

theorem select_dimension_run (input : RAMInput) (f : ℕ → Cmd) (n d : ℕ) (hd : d ≤ n)
    (s t : Store) (steps : ℕ) (hreg : s.nr 68 = d) (hr : Run input (f d) (marked s d) t steps) :
    ∃ cost, Run input (selectDimension f n) s t cost ∧ cost ≤ steps + 2 * n + 3 := by
  induction n generalizing s with
  | zero =>
    obtain rfl : d = 0 := by omega
    exact ⟨_, Run.seq (Run.atom ⟨.natConst 69 0, trivial⟩ s) hr, by omega⟩
  | succ n ih =>
    let p := marked s (n + 1)
    have hp : Run input (.atom ⟨.natConst 69 (n + 1), trivial⟩) s p 1 := Run.atom _ s
    by_cases he : d = n + 1
    · rw [he] at hreg hr
      have hg : (Guard.nat .eq 68 69).eval p = true := by simp [p, marked, Guard.eval, natTest, hreg]
      exact ⟨_, Run.seq hp (Run.branchTrue hg hr), by omega⟩
    · have hg : (Guard.nat .eq 68 69).eval p = false := by simp [p, marked, Guard.eval, natTest, hreg, he]
      have hm : marked p d = marked s d := by simp [p, marked, Function.update_idem]
      obtain ⟨c, hh, hn⟩ := ih (by omega) p (by simpa [p, marked] using hreg) (hm ▸ hr)
      exact ⟨_, Run.seq hp (Run.branchFalse hg hh), by omega⟩

def dimensionOps : List Atom := [⟨.natConst 68 4, trivial⟩, ⟨.loadNat 68 68, trivial⟩]

def dimensioned (S : Store) : Store := {S with nr := Function.update S.nr 68 (S.nm 4)}

theorem dimension_run (input : RAMInput) (s : Store) :
    Run input (.atoms dimensionOps) s (dimensioned s) 2 := by
  have h : evalAtoms input dimensionOps s = dimensioned s := by
    simp [evalAtoms, dimensionOps, dimensioned, Atom.eval, Store.at, Store.ofRAM, ramStep, Function.update_idem]
  exact h ▸ run_atoms input dimensionOps s

theorem retrieve_length {k : ℕ} (A : ClockCall k) (t : ℕ) (P : List ℕ) (hp : retrieve A t = some P) :
    P.length ≤ (A.d * A.q + 1) * ((incidentVertices A.I).length + 1) + 1 := by
  obtain ⟨ticks, edges, htrace, hfuel⟩ := retrieveFuel_backtrace A (constructTable A) _
    ⟨[t], fun _ => 0, fun _ => 1 / (8 * (k : ℝ))⟩ P hp
  have hlen := (backtrace_counts htrace).2
  simp only [List.length_singleton] at hlen
  omega

theorem retrieve_buffer {k : ℕ} (A : ClockCall k) (hd : 1 ≤ A.d) (hq : 1 ≤ A.q)
    (t : ℕ) (P : List ℕ) (hp : retrieve A t = some P) :
    P.length ≤ 2 * ((A.d + 4) * A.I.graph.n * A.q ^ A.d) + 1 := by
  have he := retrieve_length A t P hp
  have hn := ParentQuery.incident_length_le_n A.I
  have hpos := A.I.source_valid
  have hpow : A.q ≤ A.q ^ A.d := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n := A.q) (by omega) hd
  have hleft : A.d * A.q + 1 ≤ (A.d + 4) * A.q ^ A.d := by
    have hx := Nat.mul_le_mul_left A.d hpow
    nlinarith
  have hright : (incidentVertices A.I).length + 1 ≤ 2 * A.I.graph.n := by omega
  have h := Nat.mul_le_mul hleft hright
  nlinarith

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured
open Mission.Query (prependResult prependCmd prepend_run)

def QuerySpace {k : ℕ} (I : MultiInstance k) (ε : ℝ) (snap : RAMState) : Prop :=
  ∀ r A, (outerCalls I ε)[r]? = some A → extent A (callBase I ε r) ≤ snap.nm 6

def bufferOps : List Atom :=
  [⟨.natConst 65 6, trivial⟩, ⟨.loadNat 66 65, trivial⟩, ⟨.natOp .add 3 58 58, trivial⟩,
   ⟨.natOp .add 3 66 3, trivial⟩, ⟨.natConst 65 4, trivial⟩, ⟨.natOp .add 3 3 65, trivial⟩,
   ⟨.natConst 2 0, trivial⟩, ⟨.natConst 40 1, trivial⟩, ⟨.natConst 65 1, trivial⟩, ⟨.loadNat 5 65, trivial⟩]

def bufferCmd : Cmd := .seq (.atoms bufferOps) prependCmd

theorem buffer_fields (input : RAMInput) (s : Store) :
    let t := evalAtoms input bufferOps s
    t.nr 3 = s.nm 6 + 2 * s.nr 58 + 4 ∧ t.nr 2 = 0 ∧ t.nr 40 = 1 ∧ t.nr 5 = s.nm 1 ∧
      (∀ j, j ≠ 2 → j ≠ 3 → j ≠ 5 → j ≠ 40 → j ≠ 65 → j ≠ 66 → t.nr j = s.nr j) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  simp +contextual [evalAtoms, bufferOps, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, two_mul]

theorem buffer_ready {k : ℕ} (A : ClockCall k) (base v : ℕ) (input : RAMInput) (s : Store)
    (hc : Cursor A base v ⟨[v], fun _ => 0, fun _ => 1 / (8 * (k : ℝ))⟩ s)
    (hf : s.nr 0 = v) (hz : s.nr 30 = 0) (hq : s.nr 57 = A.q)
    (hs : s.nr 59 = (A.d + 4) * A.I.graph.n) (hsource : s.nm 1 = A.I.source)
    (hi : Image A base s) (hb : extent A base ≤ s.nm 6) :
    ∃ t, Run input bufferCmd s t 13 ∧
      Ready A base v ⟨[v], fun _ => 0, fun _ => 1 / (8 * (k : ℝ))⟩ t ∧
      t.nr 3 = s.nm 6 + 2 * s.nr 58 + 3 := by
  let p := evalAtoms input bufferOps s
  obtain ⟨hbase, hcount, hlive, hsrc, hn, hrr, hnm, hrm⟩ := buffer_fields input s
  have hcur : Cursor A base v ⟨[v], fun _ => 0, fun _ => 1 / (8 * (k : ℝ))⟩ p := by
    refine ⟨(hn 49 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.address,
      ?_, fun r => (congrFun hrr _).trans (hc.coeff r), ?_, (congrFun hrr _).trans hc.factor,
      (hn 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.one⟩
    · intro r; have hh := state_large r.val
      exact (hn _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hc.counts r)
    · intro r; have hh := stride_large r.val
      exact (hn _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hc.strides r)
  have pfront : p.nr 0 = v := (hn _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hf
  have proom : extent A base < p.nr 3 := by change extent A base < (evalAtoms input bufferOps s).nr 3; omega
  have pempty : ParentQuery.Output [] p := ⟨hcount, by intro _ hj; simp at hj⟩
  have hvertices := ParentQuery.output_prepend p v [] pfront pempty (by omega)
  have keep (j : ℕ) (hj : j ≠ 2) (hj' : j ≠ 3) : (prependResult p).nr j = p.nr j := by
    simp [prependResult, Function.update_of_ne hj, Function.update_of_ne hj']
  refine ⟨prependResult p, Run.seq (run_atoms input bufferOps s) (prepend_run input p hcur.one),
    ⟨?_, (keep 0 (by decide) (by decide)).trans pfront, (keep 5 (by decide) (by decide)).trans (hsrc.trans hsource),
      ?_, (keep 40 (by decide) (by decide)).trans hlive, ?_, ?_, hvertices, (hi.frame hnm hrm).prepend proom⟩, ?_⟩
  · refine ⟨(keep 49 (by decide) (by decide)).trans hcur.address, ?_, hcur.coeff, ?_, hcur.factor,
      (keep 31 (by decide) (by decide)).trans hcur.one⟩
    · intro r; have hh := state_large r.val; exact (keep _ (by omega) (by omega)).trans (hcur.counts r)
    · intro r; have hh := stride_large r.val; exact (keep _ (by omega) (by omega)).trans (hcur.strides r)
  · exact (keep _ (by decide) (by decide)).trans
      ((hn _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz)
  · exact (keep _ (by decide) (by decide)).trans
      ((hn _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq)
  · exact (keep _ (by decide) (by decide)).trans
      ((hn _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs)
  · have hp : p.nr 3 = s.nm 6 + 2 * s.nr 58 + 4 := hbase
    simp [prependResult, hp]

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery

def publicLimit (k n d q calls : ℕ) :=
  32 + 2 * k + 8 * n + calls * (4 + (d + 4) * n * q ^ d)

theorem space_of_limit {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (snap : RAMState)
    (h : snap.nm 6 = publicLimit k I.graph.n (clockCoordinates I).length (multiQ k ε) (outerCalls I ε).length) :
    QuerySpace I ε snap := by
  intro r A hr
  obtain ⟨hI, hδ, _⟩ := outerCalls_fields I ε hε A (List.mem_of_getElem? hr)
  have hi : r < (outerCalls I ε).length := List.getElem?_eq_some_iff.mp hr |>.1
  have hd : A.d = (clockCoordinates I).length := by simp [ClockCall.d, ClockCall.coords, hI]
  have hq : A.q = multiQ k ε := by simp [ClockCall.q, multiQ, hδ]
  let w := ((clockCoordinates I).length + 4) * I.graph.n * multiQ k ε ^ (clockCoordinates I).length
  have he := Nat.mul_le_mul_right (4 + w) (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at he
  simp only [h, extent, publicLimit, callBase, hI, hd, hq]
  dsimp [w] at he
  omega

theorem preserves_encoding {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s t : RAMState)
    (enc : EncodesMultiOutput I ε s) (hn : ∀ j, j ≠ 6 → t.nm j = s.nm j) (hr : t.rm = s.rm) :
    EncodesMultiOutput I ε t := by
  obtain ⟨hq, hs, hN, hk, hd, hc, hz, hh, hcoords, htargets, htree, hdata⟩ := enc
  refine ⟨(hn 0 (by decide)).trans hq, (hn 1 (by decide)).trans hs, (hn 2 (by decide)).trans hN,
    (hn 3 (by decide)).trans hk, (hn 4 (by decide)).trans hd, (hn 5 (by decide)).trans hc,
    (congrFun hr 0).trans hz, (congrFun hr 1).trans hh, ?_, ?_, ?_, ?_⟩
  · intro r; exact (hn _ (by omega)).trans (hcoords r)
  · intro v hv
    have hslot : 32 ≤ targetSlot k v := by unfold targetSlot; omega
    obtain ⟨hf, hval, hcall⟩ := htargets v hv
    exact ⟨(hn _ (by omega)).trans hf, fun d h => (congrFun hr _).trans (hval d h),
      fun r h => (hn _ (by omega)).trans (hcall r h)⟩
  · intro h v hv
    exact (hn _ (by unfold targetSlot; omega)).trans (htree h v hv)
  · intro r A hA
    obtain ⟨hv, htag, htable⟩ := hdata r A hA
    have hb : 32 ≤ callBase I ε r := by unfold callBase; omega
    refine ⟨(congrFun hr _).trans hv, (hn _ (by omega)).trans htag, ?_⟩
    intro v hinc i hvalid
    obtain ⟨hval, ht, hp, hrank, hpgf⟩ := htable v hinc i hvalid
    dsimp only
    exact ⟨(congrFun hr _).trans hval, (hn _ (by omega)).trans ht, (hn _ (by omega)).trans hp,
      (hn _ (by omega)).trans hrank, fun u he j => (congrFun hr _).trans (hpgf u he j)⟩

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.SpaceRAM
open Mission.Structured TableQuery

noncomputable def shaped (k d : ℕ) (input : RAMInput) (s : Store) : Store :=
  added 49 60 8 (added 58 60 (d + 4) (evalAtoms input (shapeOps k) s))
def countOps : List Atom :=
  [⟨.natConst 65 4, trivial⟩, ⟨.natOp .add 58 65 58, trivial⟩, ⟨.natConst 65 5, trivial⟩, ⟨.loadNat 57 65, trivial⟩]
def finishOps : List Atom :=
  [⟨.natOp .add 58 49 58, trivial⟩, ⟨.natConst 65 6, trivial⟩, ⟨.storeNat 65 58, trivial⟩]
def dimCmd (k d : ℕ) : Cmd := .seq (shapeCmd k d) (.seq (powers d) (.seq (.atoms countOps) (.seq productCmd (.atoms finishOps))))
def cmd (k : ℕ) : Cmd := .seq (.atoms dimensionOps) (selectDimension (dimCmd k) k)

theorem shape_run (k d : ℕ) (input : RAMInput) (s : Store) :
    let t := shaped k d input s
    Run input (shapeCmd k d) s t (d + 19) ∧ t.nr 58 = (d + 4) * s.nm 2 ∧ t.nr 57 = s.nm 0 ∧
      t.nr 49 = 32 + 2 * k + 8 * s.nm 2 ∧ t.nr 31 = 1 ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  have he := Run.seq (run_atoms input (shapeOps k) s) (Run.seq
    (add_copies_run input 58 60 (by decide) (d + 4) (evalAtoms input (shapeOps k) s))
    (add_copies_run input 49 60 (by decide) 8 _))
  have hlen : (shapeOps k).length + ((d + 4) + 8) = d + 19 := by change 7 + ((d + 4) + 8) = _; omega
  refine ⟨hlen ▸ he, ?_⟩
  simp [shaped, added, shapeOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep]

theorem dim_run (k d : ℕ) (input : RAMInput) (s : Store) :
    ∃ out, Run input (dimCmd k d) s out (d + 30 + d * (4 * s.nm 0 + 5) + 4 * s.nm 5) ∧
      out.nm = Function.update s.nm 6 (publicLimit k (s.nm 2) d (s.nm 0) (s.nm 5)) ∧ out.rm = s.rm := by
  let p := shaped k d input s
  obtain ⟨hp, hwidth, hq, hbase, hpone, hpn, hpr⟩ := shape_run k d input s
  obtain ⟨w, hpow, hvol, _, hregs, _, hnm, hrm⟩ := powers_run input p d hpone
  have hi (j : ℕ) (hh : j < 100) (h58 : j ≠ 58) (h61 : j ≠ 61) (h62 : j ≠ 62) :=
    hregs j (fun r _ => by have := stride_large r; omega) h58 h61 h62
  have hb : w.nr 49 = 32 + 2 * k + 8 * s.nm 2 := (hi 49 (by decide) (by decide) (by decide) (by decide)).trans hbase
  have h1 : w.nr 31 = 1 := (hi 31 (by decide) (by decide) (by decide) (by decide)).trans hpone
  have hwq : p.nr 57 = s.nm 0 := hq
  have hww : p.nr 58 = (d + 4) * s.nm 2 := hwidth
  rw [hwq, hww] at hvol
  rw [hwq] at hpow
  let c := evalAtoms input countOps w
  have hc : c.nr 57 = s.nm 5 ∧ c.nr 58 = 4 + (d + 4) * s.nm 2 * s.nm 0 ^ d ∧
      c.nr 49 = 32 + 2 * k + 8 * s.nm 2 ∧ c.nr 31 = 1 ∧ c.nm = s.nm ∧ c.rm = s.rm := by
    simp [c, countOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, h1, hvol, hb,
      hnm.trans hpn, hrm.trans hpr]
  obtain ⟨hcalls, hval, h49, hone, hcn, hcr⟩ := hc
  let t := productResult c
  have ht := product_run input c hone
  rw [hcalls] at ht
  have hstore : (evalAtoms input finishOps t).nm = Function.update s.nm 6
      (publicLimit k (s.nm 2) d (s.nm 0) (s.nm 5)) := by
    simp [t, productResult, partialProduct, finishOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
      evalNat, hcalls, hval, h49, hcn, publicLimit]
  have hex := Run.seq hp (Run.seq hpow (Run.seq (run_atoms input countOps w) (Run.seq ht (run_atoms input finishOps t))))
  have hcost : d + 19 + (d * (4 * s.nm 0 + 5) + (countOps.length + (4 * s.nm 5 + 4 + finishOps.length))) =
      d + 30 + d * (4 * s.nm 0 + 5) + 4 * s.nm 5 := by
    change d + 19 + (_ + (4 + (_ + 4 + 3))) = _; omega
  exact ⟨_, hcost ▸ hex, hstore, hcr⟩

theorem reserve_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (input : RAMInput) (s : Store)
    (henc : EncodesMultiOutput I ε (s.at 0)) :
    ∃ t cost, Run input (cmd k) s t cost ∧ EncodesMultiOutput I ε (t.at 0) ∧ QuerySpace I ε (t.at 0) ∧
      cost ≤ 4 * k * multiQ k ε + 8 * k + 35 + 4 * (outerCalls I ε).length := by
  let d := (clockCoordinates I).length
  let p := dimensioned s
  let v := marked p d
  have hq : s.nm 0 = multiQ k ε := henc.1
  have hn : s.nm 2 = I.graph.n := henc.2.2.1
  have hd : s.nm 4 = d := henc.2.2.2.2.1
  have hc : s.nm 5 = (outerCalls I ε).length := henc.2.2.2.2.2.1
  have hdk : d ≤ k := clockCoordinates_length_le I
  obtain ⟨t, ht, htmem, htr⟩ := dim_run k d input v
  have htag : p.nr 68 = d := by simp [p, dimensioned, hd]
  obtain ⟨cost, hrun, hcost⟩ := select_dimension_run input (dimCmd k) k d hdk p t _ htag ht
  have hset : t.nm = Function.update s.nm 6 (publicLimit k I.graph.n d (multiQ k ε) (outerCalls I ε).length) := by
    change t.nm = Function.update s.nm 6 (publicLimit k (s.nm 2) d (s.nm 0) (s.nm 5)) at htmem
    rwa [hn, hq, hc] at htmem
  have he := preserves_encoding I ε (s.at 0) (t.at 0) henc
    (fun j hj => (congrFun hset j).trans (Function.update_of_ne hj _ _)) htr
  have hwrite : (t.at 0).nm 6 = publicLimit k I.graph.n d (multiQ k ε) (outerCalls I ε).length :=
    (congrFun hset 6).trans (Function.update_self _ _ _)
  refine ⟨t, 2 + cost, Run.seq (dimension_run input s) hrun, he, space_of_limit I ε hε _ hwrite, ?_⟩
  change cost ≤ d + 30 + d * (4 * s.nm 0 + 5) + 4 * s.nm 5 + 2 * k + 3 at hcost
  rw [hq, hc] at hcost
  have hm := Nat.mul_le_mul_right (multiQ k ε) hdk
  nlinarith

end NearLinearRSP.TwoResources.Supplement.SpaceRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement

noncomputable def thresholdLog {k : ℕ} (I : MultiInstance k) : ℝ :=
  1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio (lengthInstance I))

theorem thresholdLog_ge_one {k : ℕ} (I : MultiInstance k) : 1 ≤ thresholdLog I := by
  have hn : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hr := one_le_aspectRatio (lengthInstance I)
  have hprod : 1 ≤ (max 2 I.graph.n : ℕ) * aspectRatio (lengthInstance I) := by nlinarith
  have hl := Real.log_nonneg hprod
  unfold thresholdLog
  linarith

theorem guessesAux_length_le (δ cap : ℝ) (fuel : ℕ) (L : ℝ) :
    (guessesAux δ cap fuel L).length ≤ fuel := by
  induction fuel generalizing L with
  | zero => simp [guessesAux]
  | succ n ih =>
    rw [guessesAux]
    split_ifs
    · simp
    · simpa only [List.length_cons] using Nat.add_le_add_right (ih (L * (1 + δ))) 1

theorem log_grid_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ε / 8 ≤ Real.log (1 + ε / 4) := by
  have hlog := Real.le_log_one_add_of_nonneg (show 0 ≤ ε / 4 by linarith)
  have hden : 0 < ε / 4 + 2 := by linarith
  have hlow : ε / 8 ≤ 2 * (ε / 4) / (ε / 4 + 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  exact hlow.trans hlog

theorem positiveGuesses_length_bound {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ((positiveGuesses I ε).length : ℝ) ≤ 11 * thresholdLog I / ε := by
  have hlog := thresholdLog_ge_one I
  unfold positiveGuesses
  split_ifs with hempty
  · simp only [List.length_nil, Nat.cast_zero]
    exact div_nonneg (by linarith) hε.le
  · have hne : positiveLengths (lengthInstance I) ≠ [] := by
      intro he
      apply hempty
      exact Or.inl (by simp [he])
    let a := firstPositiveLength (lengthInstance I)
    let b := largestLength (lengthInstance I)
    let y := (I.graph.n : ℝ) * b / a
    let z := Real.log (1 + ε / 4)
    have ha : 0 < a := firstPositiveLength_pos _
    have hab : a ≤ b := firstPositiveLength_le_largestLength _ hne
    have hn : (1 : ℝ) ≤ I.graph.n := by exact_mod_cast (show 1 ≤ I.graph.n by have := I.source_valid; omega)
    have hy : 1 ≤ y := by
      apply (le_div_iff₀ ha).mpr
      nlinarith
    have hR : aspectRatio (lengthInstance I) = b / a := by
      simp only [aspectRatio, List.isEmpty_iff, if_neg hne, a, b]
    have hyN : y ≤ (max 2 I.graph.n : ℕ) * aspectRatio (lengthInstance I) := by
      rw [hR]
      have hnN : (I.graph.n : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast le_max_right 2 I.graph.n
      dsimp [y]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hnN (div_nonneg (ha.le.trans hab) ha.le)
    have hln : 0 ≤ Real.log y := Real.log_nonneg hy
    have hlnN : Real.log y ≤ thresholdLog I - 1 := by
      have hh := Real.log_le_log (by linarith : 0 < y) hyN
      simpa [thresholdLog] using hh
    have hz : 0 < z := Real.log_pos (by linarith)
    have hzlow : ε / 8 ≤ z := log_grid_lower ε hε hε1
    have hratio : Real.log y / z ≤ 8 * (thresholdLog I - 1) / ε := by
      apply (div_le_iff₀ hz).mpr
      have hprod := mul_le_mul_of_nonneg_left hzlow (by linarith : 0 ≤ thresholdLog I - 1)
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hε).mpr
      have hh := mul_le_mul_of_nonneg_right hlnN hε.le
      nlinarith
    have hc := (Nat.ceil_lt_add_one (div_nonneg hln hz.le)).le
    have hlen := guessesAux_length_le (ε / 4) ((I.graph.n : ℝ) * b)
      (Nat.ceil (Real.log y / z) + 2) a
    have hlenR : ((guessesAux (ε / 4) ((I.graph.n : ℝ) * b)
      (Nat.ceil (Real.log y / z) + 2) a).length : ℝ) ≤ (Nat.ceil (Real.log y / z) : ℝ) + 2 := by
      exact_mod_cast hlen
    change ((guessesAux (ε / 4) ((I.graph.n : ℝ) * b)
      (Nat.ceil (Real.log y / z) + 2) a).length : ℝ) ≤ _
    have hsmall : 8 * (thresholdLog I - 1) / ε + 3 ≤ 11 * thresholdLog I / ε := by
      apply (le_div_iff₀ hε).mpr
      have hmul : (8 * (thresholdLog I - 1) / ε) * ε = 8 * (thresholdLog I - 1) := by
        field_simp
      nlinarith
    exact (hlenR.trans (by linarith)).trans hsmall

theorem outerCalls_length_bound {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ((outerCalls I ε).length : ℝ) ≤ 12 * thresholdLog I / ε := by
  have hl := positiveGuesses_length_bound I ε hε hε1
  have hlog := thresholdLog_ge_one I
  have hunit : 1 ≤ thresholdLog I / ε := (le_div_iff₀ hε).mpr (by linarith)
  unfold outerCalls
  split_ifs
  · simp only [List.length_cons, List.length_map, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ 11 * thresholdLog I / ε + thresholdLog I / ε := add_le_add hl hunit
      _ = _ := by ring
  · simp only [List.length_nil, Nat.cast_zero]
    exact div_nonneg (by linarith) hε.le

theorem multiQ_bound (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((multiQ k ε + 1 : ℕ) : ℝ) ≤ (8192 * (k : ℝ) + 2) / ε ^ 2 := by
  have he : 512 * (k : ℝ) / (ε / 4) ^ 2 = 8192 * (k : ℝ) / ε ^ 2 := by
    field_simp
    ring
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 512 * (k : ℝ) / (ε / 4) ^ 2 by positivity)).le
  rw [he] at hc
  have hh : (multiQ k ε : ℝ) ≤ 8192 * (k : ℝ) / ε ^ 2 + 1 := by
    simpa only [multiQ, ticks, he] using hc
  rw [Nat.cast_add, Nat.cast_one]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg ε)
  have hcancel : (8192 * (k : ℝ) / ε ^ 2) * ε ^ 2 = 8192 * (k : ℝ) := by field_simp
  nlinarith

theorem multiQ_power_bound (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((multiQ k ε + 1 : ℕ) : ℝ) ^ (2 * k) ≤
      (8192 * (k : ℝ) + 2) ^ (2 * k) / ε ^ (4 * k) := by
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (multiQ k ε + 1 : ℕ) by positivity)
    (multiQ_bound k ε hε hε1) (2 * k)
  rw [div_pow, ← pow_mul] at hp
  simpa only [show 2 * (2 * k) = 4 * k by omega] using hp

theorem call_grid_work_bound {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ((outerCalls I ε).length : ℝ) * ((multiQ k ε + 1 : ℕ) : ℝ) ^ (2 * k) ≤
      (12 * (8192 * (k : ℝ) + 2) ^ (2 * k)) * thresholdLog I / ε ^ (4 * k + 1) := by
  have hl := outerCalls_length_bound I ε hε hε1
  have hq := multiQ_power_bound k ε hε hε1
  have hlog := thresholdLog_ge_one I
  calc
    _ ≤ (12 * thresholdLog I / ε) * ((8192 * (k : ℝ) + 2) ^ (2 * k) / ε ^ (4 * k)) :=
      mul_le_mul hl hq (by positivity) (div_nonneg (by linarith) hε.le)
    _ = _ := by rw [pow_succ]; field_simp

theorem scaled_grid_work_bound {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    (max 1 I.graph.edges.length : ℕ) * (1 + Real.log (max 2 I.graph.n : ℕ)) *
      (((outerCalls I ε).length : ℝ) * ((multiQ k ε + 1 : ℕ) : ℝ) ^ (2 * k)) ≤
      (12 * (8192 * (k : ℝ) + 2) ^ (2 * k)) * multiScale I ε := by
  have hn : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hl := Real.log_nonneg hn
  have h := mul_le_mul_of_nonneg_left (call_grid_work_bound I ε hε hε1)
    (show 0 ≤ (max 1 I.graph.edges.length : ℕ) * (1 + Real.log (max 2 I.graph.n : ℕ)) by positivity)
  calc
    _ ≤ _ := h
    _ = _ := by unfold multiScale thresholdLog; ring

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem multiScale_lower {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) : 1 / ε ^ 2 ≤ multiScale I ε := by
  have hm : (1 : ℝ) ≤ (max 1 I.graph.edges.length : ℕ) := by exact_mod_cast le_max_left 1 I.graph.edges.length
  have hn : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hl := Real.log_nonneg hn
  have hlog := thresholdLog_ge_one I
  have hprod : 1 ≤ (max 1 I.graph.edges.length : ℕ) *
      (1 + Real.log (max 2 I.graph.n : ℕ)) * thresholdLog I := by
    have hm' : 1 ≤ (max 1 I.graph.edges.length : ℕ) * (1 + Real.log (max 2 I.graph.n : ℕ)) := by nlinarith
    nlinarith
  have hp : ε ^ (4 * k + 1) ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1.le (by omega)
  calc
    _ ≤ 1 / ε ^ (4 * k + 1) := one_div_le_one_div_of_le (pow_pos hε _) hp
    _ ≤ _ := (div_le_div_iff_of_pos_right (pow_pos hε _)).mpr hprod

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.SpaceRAM
open Mission.Structured TableQuery

def reserveCoefficient (k : ℕ) : ℝ :=
  4 * (k : ℝ) * (8192 * k + 2) + (8 * k + 35) + 4 * (12 * (8192 * k + 2) ^ (2 * k))

theorem scale_one {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    1 ≤ multiScale I ε := by
  apply le_trans _ (multiScale_lower I hk ε hε hε1)
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  nlinarith [mul_pos hε (sub_pos.mpr hε1)]

theorem calls_le_scale {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((outerCalls I ε).length : ℝ) ≤ (12 * (8192 * (k : ℝ) + 2) ^ (2 * k)) * multiScale I ε := by
  have hm : (1 : ℝ) ≤ (max 1 I.graph.edges.length : ℕ) := by exact_mod_cast le_max_left 1 I.graph.edges.length
  have hn : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hlog : 1 ≤ 1 + Real.log (max 2 I.graph.n : ℕ) := by linarith [Real.log_nonneg hn]
  have hfac := one_le_mul_of_one_le_of_one_le hm hlog
  have hq : (1 : ℝ) ≤ ((multiQ k ε + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ multiQ k ε + 1 by omega)
  have hp := one_le_pow₀ (n := 2 * k) hq
  calc
    _ ≤ ((outerCalls I ε).length : ℝ) * ((multiQ k ε + 1 : ℕ) : ℝ) ^ (2 * k) :=
      le_mul_of_one_le_right (by positivity) hp
    _ ≤ _ := (le_mul_of_one_le_left (by positivity) hfac).trans (scaled_grid_work_bound I ε hε hε1)

theorem reserve_bound {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : n ≤ 4 * k * multiQ k ε + 8 * k + 35 + 4 * (outerCalls I ε).length) :
    (n : ℝ) ≤ reserveCoefficient k * multiScale I ε := by
  have hq0 := multiQ_bound k ε hε hε1
  rw [Nat.cast_add, Nat.cast_one] at hq0
  have hq : (multiQ k ε : ℝ) ≤ (8192 * (k : ℝ) + 2) * multiScale I ε := by
    calc
      _ ≤ (8192 * (k : ℝ) + 2) / ε ^ 2 := by linarith
      _ = _ * (1 / ε ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (multiScale_lower I hk ε hε hε1) (by positivity)
  have ha := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4 * (k : ℝ) by positivity)
  have hb := le_mul_of_one_le_right (show 0 ≤ 8 * (k : ℝ) + 35 by positivity) (scale_one I hk ε hε hε1)
  have hc := mul_le_mul_of_nonneg_left (calls_le_scale I ε hε hε1) (show (0 : ℝ) ≤ 4 by norm_num)
  have ht : (n : ℝ) ≤ 4 * (k : ℝ) * (multiQ k ε : ℝ) + 8 * k + 35 + 4 * ((outerCalls I ε).length : ℝ) := by
    exact_mod_cast hn
  unfold reserveCoefficient
  linarith only [ht, ha, hb, hc]

end NearLinearRSP.TwoResources.Supplement.SpaceRAM

end

section

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement

def MultiResourceGoal : Prop :=
    ∀ k : ℕ, 2 ≤ k →
      ∃ preprocessing retrieval : Program, ∃ K : ℝ, 0 < K ∧
        ∀ (I : MultiInstance k) (ε : ℝ), 0 < ε → ε < 1 →
          ∃ (steps : ℕ) (snapshot : RAMState),
            Execution preprocessing (multiInput I ε) initialState snapshot steps ∧
            (steps : ℝ) ≤ K * multiScale I ε ∧ EncodesMultiOutput I ε snapshot ∧
            ∀ t : ℕ, t < I.graph.n →
              multiDistance snapshot t = selectedDistance I ε t ∧
              (∃ (querySteps : ℕ) (out : RAMState),
                Execution retrieval (multiInput I ε) (multiQueryStart snapshot t) out querySteps ∧
                multiQueryPath out = selectedPath I ε t ∧
                (querySteps : ℝ) ≤ K * multiRetrievalScale k ε (selectedPath I ε t)) ∧
              (∀ d : ℝ, multiDistance snapshot t = some d →
                ∃ P : List ℕ, selectedPath I ε t = some P ∧
                  RelaxedPath I ε t P ∧ pathWeight I.length P ≤ d ∧
                  ∀ R : List ℕ, ExactFeasible I t R → d ≤ (1 + ε) * pathWeight I.length R) ∧
              ((∃ R : List ℕ, ExactFeasible I t R) →
                (multiDistance snapshot t).isSome = true) ∧
              (∀ P : List ℕ, selectedPath I ε t = some P → RelaxedPath I ε t P)

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement

def MachineRealization : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ preprocessing retrieval : Program, ∃ K : ℝ, 0 < K ∧
      ∀ (I : MultiInstance k) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (steps : ℕ) (snapshot : RAMState),
          Execution preprocessing (multiInput I ε) initialState snapshot steps ∧
          (steps : ℝ) ≤ K * multiScale I ε ∧ EncodesMultiOutput I ε snapshot ∧
          ∀ t : ℕ, t < I.graph.n →
            ∃ (querySteps : ℕ) (out : RAMState),
              Execution retrieval (multiInput I ε) (multiQueryStart snapshot t) out querySteps ∧
              multiQueryPath out = selectedPath I ε t ∧
              (querySteps : ℝ) ≤ K * multiRetrievalScale k ε (selectedPath I ε t)

theorem goal_of_machineRealization (h : MachineRealization) : MultiResourceGoal := by
  intro k hk
  obtain ⟨preprocessing, retrieval, K, hK, hprograms⟩ := h k hk
  refine ⟨preprocessing, retrieval, K, hK, ?_⟩
  intro I ε hε hε1
  obtain ⟨steps, snapshot, hex, hsteps, henc, hquery⟩ := hprograms I ε hε hε1
  refine ⟨steps, snapshot, hex, hsteps, henc, ?_⟩
  intro t ht
  have hread := encoded_distance I ε snapshot henc t ht
  obtain ⟨hsound, hcomplete, hpath⟩ := selected_semantics_correct I (by omega) ε hε hε1 t
  refine ⟨hread, hquery t ht, ?_, ?_, hpath⟩
  · simpa only [hread] using hsound
  · simpa only [hread] using hcomplete

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured
open Mission.Query (prependCmd prependResult prepend_run)

theorem Cursor.prepend {k : ℕ} {A : ClockCall k} {base v : ℕ} {S : RetrievalState A.d} {s : Store}
    (h : Cursor A base v S s) : Cursor A base v S (prependResult s) := by
  refine ⟨by simpa [prependResult] using h.address, ?_, h.coeff, ?_, h.factor, by simpa [prependResult] using h.one⟩
  · intro r
    have hh := state_large r.val
    simpa [prependResult, Function.update_of_ne (show stateReg r.val ≠ 2 by omega),
      Function.update_of_ne (show stateReg r.val ≠ 3 by omega)] using h.counts r
  · intro r
    have hh := stride_large r.val
    simpa [prependResult, Function.update_of_ne (show strideReg r.val ≠ 2 by omega),
      Function.update_of_ne (show strideReg r.val ≠ 3 by omega)] using h.strides r

theorem ready_tick {k : ℕ} {A : ClockCall k} {base v : ℕ} {S : RetrievalState A.d} {s : Store}
    (h : Ready A base v S s) (r : Fin A.d) (input : RAMInput) (hr : s.nr 70 = r.val) :
    ∃ t cost, Run input (chooseTick k) s t cost ∧ Ready A base v (tickState A S r) t ∧
      t.nr 3 = s.nr 3 ∧ cost ≤ 2 * k + 4 := by
  let t := ticked (marked s r.val) r.val
  have hd : A.d ≤ k := clockCoordinates_length_le A.I
  obtain ⟨cost, hrun, hc⟩ := tick_dispatch_run input k r.val (r.isLt.trans_le hd) s h.cursor.one hr
  have low (j : ℕ) (hj : j < 69) (hne : j ≠ 49) : t.nr j = s.nr j := by
    have hh := state_large r.val
    simp [t, ticked, marked, Function.update_of_ne (show j ≠ stateReg r.val by omega),
      Function.update_of_ne hne, Function.update_of_ne (show j ≠ 69 by omega)]
  refine ⟨t, cost, hrun, ⟨tick_cursor A base v S s r h.cursor, (low 0 (by decide) (by decide)).trans h.front,
    (low 5 (by decide) (by decide)).trans h.source, (low 30 (by decide) (by decide)).trans h.zero,
    (low 40 (by decide) (by decide)).trans h.live, (low 57 (by decide) (by decide)).trans h.q,
    (low 59 (by decide) (by decide)).trans h.step, ?_, h.table.frame (by rfl) (by rfl)⟩,
    low 3 (by decide) (by decide), hc⟩
  refine ⟨(low 2 (by decide) (by decide)).trans h.output.count, ?_⟩
  change Mission.Query.StoresList s.nm (t.nr 3) S.path
  rw [low 3 (by decide) (by decide)]
  exact h.output.vertices

theorem ready_edge {k : ℕ} {A : ClockCall k} {base u v : ℕ} {S : RetrievalState A.d} {s : Store}
    (h : Ready A base v S s) (input : RAMInput) (hpred : s.nr 70 = u)
    (hp : (constructTable A v S.counts).parent = .edge u) (hu : u ∈ incidentVertices A.I)
    (hv : v ∈ incidentVertices A.I) (hi : ∀ r, S.counts r < A.q)
    (a : Fin A.d → ℕ) (xs : List (Fin A.d → ℕ)) (hbox : rectangle A S.counts = a :: xs)
    (hroom : extent A base < s.nr 3) :
    let b := selectMin (incrementScore A (constructTable A) S u v) (a :: xs) a
    ∃ t cost, Run input (.seq (edgeCmd A.d) prependCmd) s t cost ∧ Ready A base u (edgeState A S u v b) t ∧
      t.nr 3 = s.nr 3 - 1 ∧ cost ≤ (13 * A.d + 25) * (2 ^ A.d * (A.q + 1) ^ A.d) + 3 := by
  let b := selectMin (incrementScore A (constructTable A) S u v) (a :: xs) a
  have hpg (r : Fin A.d) : s.rm (s.nr 49 + 4 + r.val) = clockPGF A r u v := by
    rw [h.cursor.address]
    exact (h.table v hv S.counts hi).2.2.2 u hp r
  obtain ⟨w, n, hrun, hc, hfront, hlow, hq, hs, hn, hr, hcost⟩ :=
    edge_transition A (constructTable A) S u v base input s h.cursor h.front hpred h.zero h.q h.step hpg
      (fun i hi => (h.table u hu i hi).1) a xs hbox
  have hm := h.table.frame hn hr
  have hbase : w.nr 3 = s.nr 3 := hlow 3 (by decide) (by decide)
  have hsource := (hlow 5 (by decide) (by decide)).trans h.source
  have hzero := (hlow 30 (by decide) (by decide)).trans h.zero
  have hlive := (hlow 40 (by decide) (by decide)).trans h.live
  have hcurrent : ParentQuery.Output S.path w := ⟨(hlow 2 (by decide) (by decide)).trans h.output.count,
    by simpa only [hn, hbase] using h.output.vertices⟩
  have hb : extent A base < w.nr 3 := by omega
  have hout := ParentQuery.output_prepend w u S.path hfront hcurrent (by omega)
  refine ⟨prependResult w, n + 3, Run.seq hrun (prepend_run input w hc.one),
    ⟨hc.prepend, ?_, ?_, ?_, ?_, ?_, ?_, hout, hm.prepend hb⟩, ?_, by omega⟩
  · simpa [prependResult] using hfront
  · simpa [prependResult] using hsource
  · simpa [prependResult] using hzero
  · simpa [prependResult] using hlive
  · simpa [prependResult] using hq
  · simpa [prependResult] using hs
  · simp [prependResult, hbase]

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured
open Mission.Query (prependCmd)

def body (k d : ℕ) : Cmd := .branch (.nat .eq 0 5) ParentQuery.stopCmd
  (.seq (.atoms readParentOps) (.branch (.nat .eq 71 31) (chooseTick k) (.seq (edgeCmd d) prependCmd)))
def loop (k d : ℕ) : Cmd := .loop (.nat .lt 30 40) (body k d)
def traceBudget (k d q ticks edges : ℕ) :=
  6 + ticks * (2 * k + 14) + edges * ((13 * d + 25) * (2 ^ d * (q + 1) ^ d) + 15)

theorem trace_run {k : ℕ} (A : ClockCall k) (hδ : 0 < A.δ) (hL : 0 < A.L) (base : ℕ) (input : RAMInput)
    {S : RetrievalState A.d} {P : List ℕ} {ticks edges : ℕ} (ht : Backtrace A (constructTable A) S P ticks edges)
    (s : Store) (w : ℕ) (hhead : S.path.head? = some w) (hinc : w ∈ incidentVertices A.I)
    (h : Ready A base w S s) (hroom : extent A base + edges ≤ s.nr 3) :
    ∃ out cost, Run input (loop k A.d) s out cost ∧ ParentQuery.Output P out ∧
      cost ≤ traceBudget k A.d A.q ticks edges := by
  induction ht generalizing s w with
  | source S hi hh =>
    have hw : w = A.I.source := Option.some.inj (hhead.symm.trans hh)
    let out : Store := {s with nr := Function.update s.nr 40 0}
    have hg : (Guard.nat .lt 30 40).eval s = true := by simp [Guard.eval, natTest, h.zero, h.live]
    have hs : (Guard.nat .eq 0 5).eval s = true := by simp [Guard.eval, natTest, h.front, h.source, hw]
    have he : (Guard.nat .lt 30 40).eval out = false := by simp [out, Guard.eval, natTest]
    have hb : Run input (body k A.d) s out 3 := Run.branchTrue hs (ParentQuery.stop_run input s)
    exact ⟨out, 6, Run.loopTrue hg hb (Run.loopFalse he),
      ⟨by simpa [out] using h.output.count, by simpa [out] using h.output.vertices⟩, by simp [traceBudget]⟩
  | @tick S P ticks edges v j hi hh haway hp hj tail ih =>
    have hw : w = v := Option.some.inj (hhead.symm.trans hh)
    subst w
    let p := parentRead input s
    have hread : Run input (.atoms readParentOps) s p 3 := run_atoms input readParentOps s
    obtain ⟨hready, htag, hparent, hbase⟩ := ready_parentRead h input hinc hi
    have hsel : p.nr 70 = j := by simpa only [hp, multiParentPayload] using hparent
    obtain ⟨t, n, hr, hnext, htbase, hc⟩ := ready_tick hready ⟨j, hj⟩ input hsel
    obtain ⟨out, cost, ht, ho, hcost⟩ := ih t v hh hinc hnext (by omega)
    have hg : (Guard.nat .lt 30 40).eval s = true := by simp [Guard.eval, natTest, h.zero, h.live]
    have hs : (Guard.nat .eq 0 5).eval s = false := by simp [Guard.eval, natTest, h.front, h.source, haway]
    have he : (Guard.nat .eq 71 31).eval p = true := by
      simp [p, Guard.eval, natTest, htag, hp, multiParentTag, hready.cursor.one]
    have hb : Run input (body k A.d) s t (1 + (3 + (1 + n + 1))) :=
      Run.branchFalse hs (Run.seq hread (Run.branchTrue he hr))
    refine ⟨out, _, Run.loopTrue hg hb ht, ho, ?_⟩
    simp only [traceBudget] at hcost ⊢
    rw [Nat.succ_mul ticks]; omega
  | @edge S P ticks edges u v a rest hi hh haway hp hbox tail ih =>
    have hw : w = v := Option.some.inj (hhead.symm.trans hh)
    subst w
    have hpar := (constructTable_parents A hδ hL S.counts hi v hinc).2
    rw [hp] at hpar
    have hu : u ∈ incidentVertices A.I := hpar.2.1
    let p := parentRead input s
    have hread : Run input (.atoms readParentOps) s p 3 := run_atoms input readParentOps s
    obtain ⟨hready, htag, hparent, hbase⟩ := ready_parentRead h input hinc hi
    have hsel : p.nr 70 = u := by simpa only [hp, multiParentPayload] using hparent
    obtain ⟨t, n, hr, hnext, htbase, hc⟩ :=
      ready_edge hready input hsel hp hu hinc hi a rest hbox (by omega)
    obtain ⟨out, cost, ht, ho, hcost⟩ := ih t u rfl hu hnext (by omega)
    have hg : (Guard.nat .lt 30 40).eval s = true := by simp [Guard.eval, natTest, h.zero, h.live]
    have hs : (Guard.nat .eq 0 5).eval s = false := by simp [Guard.eval, natTest, h.front, h.source, haway]
    have he : (Guard.nat .eq 71 31).eval p = false := by
      simp [p, Guard.eval, natTest, htag, hp, multiParentTag, hready.cursor.one]
    have hb : Run input (body k A.d) s t (1 + (3 + (1 + n))) :=
      Run.branchFalse hs (Run.seq hread (Run.branchFalse he hr))
    refine ⟨out, _, Run.loopTrue hg hb ht, ho, ?_⟩
    simp only [traceBudget] at hcost ⊢
    rw [Nat.succ_mul edges]; omega

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery

def transitionCoefficient (k : ℕ) := (13 * k + 25) * 2 ^ k + (2 * k + 35)
def tableCoefficient (k : ℕ) := transitionCoefficient k * (k + 2) + (11 * k + 50)
def retrievalCoefficient (k : ℕ) := tableCoefficient k + 24

theorem trace_scaled {k : ℕ} {A : ClockCall k} {T : MultiTable A.d} {S : RetrievalState A.d}
    {P : List ℕ} {ticks edges : ℕ} (hk : 1 ≤ k) (h : Backtrace A T S P ticks edges) :
    traceBudget k A.d A.q ticks edges ≤ transitionCoefficient k * (k + 2) * ((A.q + 1) ^ k * (P.length + 1)) := by
  let c := transitionCoefficient k
  let z := (A.q + 1) ^ A.d
  have hd : A.d ≤ k := clockCoordinates_length_le A.I
  have hz : 1 ≤ z := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ^ A.d ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hd
  have hm := Nat.mul_le_mul (show 13 * A.d + 25 ≤ 13 * k + 25 by omega) h2
  have hbase : (13 * A.d + 25) * 2 ^ A.d + 15 ≤ c := by unfold c transitionCoefficient; omega
  have he : (13 * A.d + 25) * (2 ^ A.d * z) + 15 ≤ c * z := by
    have hc := Nat.mul_le_mul_right z hbase
    have hp := Nat.mul_le_mul_left 15 hz
    nlinarith
  have ht : 2 * k + 14 ≤ c := by unfold c transitionCoefficient; omega
  have h6 : 6 ≤ c := by omega
  have h₁ := Nat.mul_le_mul_left ticks ht
  have h₂ := Nat.mul_le_mul_left edges he
  have hlocal : traceBudget k A.d A.q ticks edges ≤ c * (ticks + 1 + (edges + 1) * z) := by
    change 6 + ticks * (2 * k + 14) + edges * ((13 * A.d + 25) * (2 ^ A.d * z) + 15) ≤ _
    nlinarith
  calc
    _ ≤ _ := hlocal
    _ ≤ _ := backtrace_work_bound hk h c
    _ = _ := by simp only [c]; ring

theorem scale_nat_lower (k q len : ℕ) (hk : 1 ≤ k) : q + 1 ≤ (q + 1) ^ k * (len + 1) := by
  have hpow : q + 1 ≤ (q + 1) ^ k := by simpa only [pow_one] using Nat.pow_le_pow_right (n := q + 1) (by omega) hk
  have he := Nat.mul_le_mul_left ((q + 1) ^ k) (show 1 ≤ len + 1 by omega)
  simp only [Nat.mul_one] at he
  exact hpow.trans he

theorem table_run_cost {k : ℕ} {A : ClockCall k} {S : RetrievalState A.d} {P : List ℕ} {ticks edges : ℕ}
    (hk : 1 ≤ k) (h : Backtrace A (constructTable A) S P ticks edges) (n c : ℕ)
    (hc : c ≤ traceBudget k A.d A.q ticks edges)
    (hn : n ≤ 2 + ((2 * A.d + 24 + (A.d * (4 * A.q + 5) + 2 * A.d) + (13 + (c + 1))) + 2 * k + 3)) :
    n ≤ tableCoefficient k * ((A.q + 1) ^ k * (P.length + 1)) := by
  have hd : A.d ≤ k := clockCoordinates_length_le A.I
  have hm := Nat.mul_le_mul_right A.q hd
  have hover : n ≤ c + (11 * k + 50) * (A.q + 1) := by nlinarith
  have hscale := scale_nat_lower k A.q P.length hk
  have htotal := hc.trans (trace_scaled hk h)
  have hfixed := Nat.mul_le_mul_left (11 * k + 50) hscale
  unfold tableCoefficient
  rw [Nat.add_mul]
  omega

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.ParentQuery
open Mission.Structured
open Mission.Query (StoresList storesList_map)

def header (k : ℕ) : List Atom :=
  [ ⟨.natConst 30 0, trivial⟩,
    ⟨.natConst 31 1, trivial⟩,
    ⟨.loadNat 5 31, trivial⟩,
    ⟨.natConst 35 2, trivial⟩,
    ⟨.loadNat 36 35, trivial⟩,
    ⟨.natOp .add 36 36 36, trivial⟩,
    ⟨.natOp .add 36 36 36, trivial⟩,
    ⟨.natOp .add 36 36 36, trivial⟩,
    ⟨.natConst 32 (32 + 2 * k), trivial⟩,
    ⟨.natOp .add 3 32 36, trivial⟩,
    ⟨.natOp .add 33 0 0, trivial⟩,
    ⟨.natOp .add 33 33 33, trivial⟩,
    ⟨.natOp .add 33 32 33, trivial⟩,
    ⟨.loadNat 34 33, trivial⟩,
    ⟨.natConst 39 3, trivial⟩,
    ⟨.natConst 2 0, trivial⟩,
    ⟨.natConst 1 0, trivial⟩,
    ⟨.natConst 40 1, trivial⟩ ]

def dispatch (k : ℕ) (table : Cmd) : Cmd :=
  .seq (.atoms (header k)) (.branch (.nat .eq 34 30) .skip
    (.branch (.nat .eq 34 39) table (.seq (loopCmd k) (.atom found))))

noncomputable def start (input : RAMInput) (k : ℕ) (S : RAMState) (t : ℕ) : Store :=
  evalAtoms input (header k) (queryStore S t)

structure HeaderFields (k : ℕ) (S : RAMState) (t : ℕ) (s : Store) : Prop where
  regs : Registers (S.nm 1) t s
  unset : s.nr 1 = 0
  emptyCount : s.nr 2 = 0
  base : s.nr 3 = 32 + 2 * k + 8 * S.nm 2
  tag : s.nr 34 = S.nm (targetSlot k t)
  tableTag : s.nr 39 = 3
  memory : s.nm = S.nm

theorem header_fields (input : RAMInput) (k : ℕ) (S : RAMState) (t : ℕ) :
    HeaderFields k S t (start input k S t) := by
  have hn : S.nm 2 + S.nm 2 + (S.nm 2 + S.nm 2) +
      (S.nm 2 + S.nm 2 + (S.nm 2 + S.nm 2)) = 8 * S.nm 2 := by omega
  have ht : 32 + 2 * k + (t + t + (t + t)) = targetSlot k t := by unfold targetSlot; omega
  constructor
  · constructor <;> simp [start, header, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
      evalNat, queryStore]
  all_goals simp [start, header, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
    evalNat, queryStore, hn, ht]

theorem decode_some (S : RAMState) (P : List ℕ) (hflag : S.nr 1 = 1)
    (h : Output P (Store.ofRAM S)) : multiQueryPath S = some P := by
  have hn : S.nr 2 = P.length := h.count
  have hm : StoresList S.nm (S.nr 3) P := h.vertices
  simp [multiQueryPath, hflag, hn, storesList_map S.nm (S.nr 3) P hm]

theorem encoded_header {k : ℕ} (I : MultiInstance k) (ε : ℝ) (S : RAMState)
    (h : EncodesMultiOutput I ε S) (t : ℕ) (ht : t < I.graph.n) :
    S.nm 1 = I.source ∧ S.nm 2 = I.graph.n ∧
    S.nm (targetSlot k t) = outputTag (selectedBranch I ε t) := by
  obtain ⟨_, hs, hn, _, _, _, _, _, _, htags, _, _⟩ := h
  exact ⟨hs, hn, (htags t ht).1⟩

theorem retrieval_scale_ge (k : ℕ) (ε : ℝ) (P : Option (List ℕ)) :
    (((P.getD []).length + 1 : ℕ) : ℝ) ≤ multiRetrievalScale k ε P := by
  have hq : 1 ≤ ((multiQ k ε + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 (multiQ k ε)
  have hp := one_le_pow₀ (n := k) hq
  unfold multiRetrievalScale
  simpa using mul_le_mul_of_nonneg_right hp (show 0 ≤ (((P.getD []).length + 1 : ℕ) : ℝ) by positivity)

theorem absent_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (S : RAMState)
    (henc : EncodesMultiOutput I ε S) (t : ℕ) (ht : t < I.graph.n)
    (hb : selectedBranch I ε t = .absent) (table : Cmd) :
    ∃ steps out, Execution (dispatch k table).program (multiInput I ε) (multiQueryStart S t) out steps ∧
      multiQueryPath out = selectedPath I ε t ∧ steps ≤ 21 := by
  let input := multiInput I ε
  let s := start input k S t
  have h := header_fields input k S t
  obtain ⟨_, _, htag⟩ := encoded_header I ε S henc t ht
  have hg : (Guard.nat .eq 34 30).eval s = true := by
    simp [s, Guard.eval, natTest, h.tag, h.regs.zero, htag, hb, outputTag]
  have hrun : Run input (dispatch k table) (queryStore S t) s 20 :=
    Run.seq (run_atoms input (header k) _) (Run.branchTrue hg (Run.skip s))
  obtain ⟨steps, out, he, hn, ho⟩ := compiled_query S t hrun
  have hz : out.nr 1 = 0 := (congrArg (fun w : Store => w.nr 1) ho).trans h.unset
  exact ⟨steps, out, he, by simp [multiQueryPath, hz, selectedPath, hb], hn⟩

theorem found_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (S : RAMState)
    (henc : EncodesMultiOutput I ε S) (t : ℕ) (ht : t < I.graph.n) (table : Cmd)
    (ha : outputTag (selectedBranch I ε t) ≠ 0) (hb : outputTag (selectedBranch I ε t) ≠ 3)
    (P : List ℕ) (hwalk : Walk I.graph.n I.source (fun v => S.nm (targetSlot k v + 2)) t P)
    (hlen : P.length ≤ I.graph.n + 1) :
    ∃ steps out, Execution (dispatch k table).program (multiInput I ε) (multiQueryStart S t) out steps ∧
      multiQueryPath out = some P ∧ steps ≤ 16 * P.length + 23 := by
  let input := multiInput I ε
  let s := start input k S t
  have h := header_fields input k S t
  obtain ⟨hs, hn, htag⟩ := encoded_header I ε S henc t ht
  have hreg : Registers I.source t s := by rw [← hs]; exact h.regs
  have hpar : Parents k I.graph.n (fun v => S.nm (targetSlot k v + 2)) s :=
    fun v _ => congrFun h.memory _
  have hnil : Output [] s := ⟨h.emptyCount, by intro j hj; simp at hj⟩
  have hroom : targetSlot k I.graph.n + P.length ≤ s.nr 3 := by
    have hpos := I.source_valid
    rw [show s.nr 3 = _ from h.base, hn]
    unfold targetSlot
    omega
  obtain ⟨v, cost, hv, hvout, hc⟩ := walk_run k input hwalk s [] hreg hpar hnil hroom
  let w : Store := { v with nr := Function.update v.nr 1 1 }
  have hflag : Run input (.atom found) v w 1 := Run.atom found v
  have hno : (Guard.nat .eq 34 30).eval s = false := by
    simp [s, Guard.eval, natTest, h.tag, h.regs.zero, htag, ha]
  have hnt : (Guard.nat .eq 34 39).eval s = false := by
    simp [s, Guard.eval, natTest, h.tag, h.tableTag, htag, hb]
  have hrun : Run input (dispatch k table) (queryStore S t) w (18 + (1 + (1 + (cost + 1)))) :=
    Run.seq (run_atoms input (header k) _)
      (Run.branchFalse hno (Run.branchFalse hnt (Run.seq hv hflag)))
  obtain ⟨steps, out, he, hsteps, hout⟩ := compiled_query S t hrun
  have hwo : Output P w :=
    ⟨by simpa [w] using hvout.count, by simpa [w] using hvout.vertices⟩
  have hf : out.nr 1 = 1 := (congrArg (fun x : Store => x.nr 1) hout).trans (by simp [w])
  exact ⟨steps, out, he, decode_some out P hf (by rw [hout]; exact hwo), by omega⟩

theorem nontable_retrieval {k : ℕ} (I : MultiInstance k) (ε : ℝ) (S : RAMState)
    (henc : EncodesMultiOutput I ε S) (t : ℕ) (ht : t < I.graph.n)
    (hnt : ∀ r, selectedBranch I ε t ≠ .table r) (table : Cmd) :
    ∃ steps out, Execution (dispatch k table).program (multiInput I ε) (multiQueryStart S t) out steps ∧
      multiQueryPath out = selectedPath I ε t ∧ (steps : ℝ) ≤ 24 * multiRetrievalScale k ε (selectedPath I ε t) := by
  have liftBound (P : List ℕ) (hp : selectedPath I ε t = some P)
      (hw : Walk I.graph.n I.source (fun v => S.nm (targetSlot k v + 2)) t P)
      (hl : P.length ≤ I.graph.n + 1) (ha : outputTag (selectedBranch I ε t) ≠ 0)
      (hb : outputTag (selectedBranch I ε t) ≠ 3) :
      ∃ steps out, Execution (dispatch k table).program (multiInput I ε) (multiQueryStart S t) out steps ∧
        multiQueryPath out = selectedPath I ε t ∧ (steps : ℝ) ≤ 24 * multiRetrievalScale k ε (selectedPath I ε t) := by
    obtain ⟨s, out, he, hpout, hs⟩ := found_run I ε S henc t ht table ha hb P hw hl
    refine ⟨s, out, he, hpout.trans hp.symm, ?_⟩
    rw [hp]
    have hn : s ≤ 24 * (P.length + 1) := by omega
    have h := retrieval_scale_ge k ε (some P)
    simp only [Option.getD_some, Nat.cast_add, Nat.cast_one] at h
    exact (by exact_mod_cast hn : (s : ℝ) ≤ 24 * ((P.length : ℝ) + 1)).trans
      (mul_le_mul_of_nonneg_left h (by norm_num))
  cases hb : selectedBranch I ε t with
  | absent =>
    obtain ⟨s, out, he, hpath, hs⟩ := absent_run I ε S henc t ht hb table
    refine ⟨s, out, he, hpath, ?_⟩
    have h := retrieval_scale_ge k ε (selectedPath I ε t)
    have hs' : (s : ℝ) ≤ 21 := by exact_mod_cast hs
    push_cast at h
    linarith [Nat.cast_nonneg (α := ℝ) ((selectedPath I ε t).getD []).length]
  | source =>
    obtain ⟨P, hp, hw, hl⟩ := source_walk I ε t S hb
    exact liftBound P hp hw hl (by simp [hb, outputTag]) (by simp [hb, outputTag])
  | ordinary =>
    obtain ⟨P, hp, hw, hl⟩ := ordinary_walk I ε t S henc hb
    exact liftBound P hp hw hl (by simp [hb, outputTag]) (by simp [hb, outputTag])
  | table r => exact (hnt r hb).elim

end NearLinearRSP.TwoResources.Supplement.ParentQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def oneTable (k d : ℕ) : Cmd :=
  .seq (startTable k d) (.seq bufferCmd (.seq (loop k d) (.atom ParentQuery.found)))
def tableCmd (k : ℕ) := Cmd.seq (.atoms dimensionOps) (selectDimension (oneTable k) k)
def queryCmd (k : ℕ) := ParentQuery.dispatch k (tableCmd k)

theorem table_case_run {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (snap : RAMState) (henc : EncodesMultiOutput I ε snap) (hspace : QuerySpace I ε snap)
    (t r : ℕ) (ht : t < I.graph.n) (hb : selectedBranch I ε t = .table r)
    (s : Store) (hn : s.nm = snap.nm) (hr : s.rm = snap.rm) (hfront : s.nr 0 = t) :
    ∃ out n P, Run (multiInput I ε) (tableCmd k) s out n ∧ selectedPath I ε t = some P ∧
      out.nr 1 = 1 ∧ ParentQuery.Output P out ∧
      n ≤ tableCoefficient k * ((multiQ k ε + 1) ^ k * (P.length + 1)) := by
  let input := multiInput I ε
  obtain ⟨A, hA, hacc⟩ := selectedBranch_table_accepts I ε t r hb
  obtain ⟨hI, hδ, hL⟩ := outerCalls_fields I ε hε A (List.mem_of_getElem? hA)
  have hδ' : 0 < A.δ := by rw [hδ]; linarith
  have hinc := accepts_incident A t hacc
  obtain ⟨P, _, hp, _, _, _, _⟩ := retrieve_success A hk hδ' hL t hinc hacc
  have hpath : selectedPath I ε t = some P := by simp [selectedPath, hb, hA, hp]
  let startS : RetrievalState A.d := ⟨[t], fun _ => 0, fun _ => 1 / (8 * (k : ℝ))⟩
  obtain ⟨ticks, edges, htrace, _⟩ := retrieveFuel_backtrace A (constructTable A) _ startS P hp
  have hedges : P.length = 1 + edges := (backtrace_counts htrace).2
  have hd : 1 ≤ A.d := clockCoordinates_pos A.I (by omega)
  have hqp : 1 ≤ A.q := ticks_pos k A.δ (by omega) hδ'
  have hsize := retrieve_buffer A hd hqp t P hp
  have himg := encoded_image I ε snap henc r A hA hI
  obtain ⟨hq, hsrc, hnodes, _, hdim, _, hz, hh, _, htags, _, _⟩ := henc
  have hdim' : A.d = (clockCoordinates I).length := by simp [ClockCall.d, ClockCall.coords, hI]
  have hQ : A.q = multiQ k ε := by simp [ClockCall.q, multiQ, hδ]
  have hZ : snap.rm 0 = clockZ A := by rw [hz, clockZ, hδ]; congr 2 <;> ring
  let p := dimensioned s
  let w := marked p A.d
  have hw : w.nr 0 = t := by simpa [w, p, marked, dimensioned] using hfront
  have hpd : p.nr 68 = A.d := by simp [p, dimensioned, hn, hdim, hdim']
  have hwn : w.nm = snap.nm := hn
  have hwr : w.rm = snap.rm := hr
  obtain ⟨v, hstart, hcursor, hvq, hvs, hvol, hv0, hvz, hvn, hvr⟩ :=
    start_run A (callBase I ε r) t input w hw ((congrFun hwn _).trans ((htags t ht).2.2 r hb))
      ((congrFun hwn 2).trans (hnodes.trans (by rw [hI]))) ((congrFun hwn 0).trans (hq.trans hQ.symm))
      ((congrFun hwr 0).trans hZ) ((congrFun hwr 1).trans hh)
  have hvnm := hvn.trans hwn
  have hvrm := hvr.trans hwr
  have hfree : extent A (callBase I ε r) ≤ v.nm 6 := by rw [hvnm]; exact hspace r A hA
  obtain ⟨x, hx, hready, hx3⟩ := buffer_ready A (callBase I ε r) t input v hcursor hv0 hvz hvq hvs
    ((congrFun hvnm 1).trans (hsrc.trans (by rw [hI]))) (himg v hvnm hvrm) hfree
  have hroom : extent A (callBase I ε r) + edges ≤ x.nr 3 := by rw [hx3, hvol]; omega
  obtain ⟨y, cost, hy, hyout, hcost⟩ := trace_run A hδ' hL (callBase I ε r) input htrace x t rfl hinc hready hroom
  let out : Store := {y with nr := Function.update y.nr 1 1}
  have hflag : Run input (.atom ParentQuery.found) y out 1 := Run.atom _ y
  have htable : Run input (oneTable k A.d) w out
      ((2 * A.d + 24 + (A.d * (4 * A.q + 5) + 2 * A.d)) + (13 + (cost + 1))) :=
    Run.seq hstart (Run.seq hx (Run.seq hy hflag))
  obtain ⟨n, hdims, hn'⟩ := select_dimension_run input (oneTable k) k A.d
    (clockCoordinates_length_le A.I) p out _ hpd htable
  refine ⟨out, 2 + n, P, Run.seq (dimension_run input s) hdims, hpath, by simp [out],
    ⟨by simpa [out] using hyout.count, by simpa [out] using hyout.vertices⟩, ?_⟩
  rw [← hQ]
  exact table_run_cost hk htrace _ cost hcost (by omega)

theorem compiled_retrieval {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (snap : RAMState) (henc : EncodesMultiOutput I ε snap) (hspace : QuerySpace I ε snap)
    (t : ℕ) (ht : t < I.graph.n) :
    ∃ steps out, Execution (queryCmd k).program (multiInput I ε) (multiQueryStart snap t) out steps ∧
      multiQueryPath out = selectedPath I ε t ∧
      (steps : ℝ) ≤ (retrievalCoefficient k : ℕ) * multiRetrievalScale k ε (selectedPath I ε t) := by
  by_cases htable : ∃ r, selectedBranch I ε t = .table r
  · obtain ⟨r, hb⟩ := htable
    let input := multiInput I ε
    let s := ParentQuery.start input k snap t
    have hh := ParentQuery.header_fields input k snap t
    obtain ⟨_, _, htag⟩ := ParentQuery.encoded_header I ε snap henc t ht
    obtain ⟨v, cost, P, hrun, hpath, hfound, hvertices, hc⟩ :=
      table_case_run I hk ε hε snap henc hspace t r ht hb s hh.memory rfl hh.regs.front
    have hno : (Guard.nat .eq 34 30).eval s = false := by
      simp [s, Guard.eval, natTest, hh.tag, hh.regs.zero, htag, hb, outputTag]
    have hyes : (Guard.nat .eq 34 39).eval s = true := by
      simp [s, Guard.eval, natTest, hh.tag, hh.tableTag, htag, hb, outputTag]
    have he : Run input (queryCmd k) (queryStore snap t) v (18 + (1 + (1 + cost + 1))) :=
      Run.seq (run_atoms input (ParentQuery.header k) _) (Run.branchFalse hno (Run.branchTrue hyes hrun))
    obtain ⟨steps, out, hex, hs, hout⟩ := compiled_query snap t he
    have hf : out.nr 1 = 1 := (congrArg (fun z : Store => z.nr 1) hout).trans hfound
    have hp := ParentQuery.decode_some out P hf (by rw [hout]; exact hvertices)
    refine ⟨steps, out, hex, hp.trans hpath.symm, ?_⟩
    have hpos := scale_nat_lower k (multiQ k ε) P.length hk
    have hl : 1 ≤ (multiQ k ε + 1) ^ k * (P.length + 1) := by omega
    have hmul := Nat.mul_le_mul_left 24 hl
    have hbound : steps ≤ retrievalCoefficient k * ((multiQ k ε + 1) ^ k * (P.length + 1)) := by
      unfold retrievalCoefficient; rw [Nat.add_mul]; omega
    rw [hpath]
    unfold multiRetrievalScale
    simp only [Option.getD_some]
    exact_mod_cast hbound
  · have hnt : ∀ r, selectedBranch I ε t ≠ .table r := fun r h => htable ⟨r, h⟩
    obtain ⟨steps, out, he, hp, hs⟩ := ParentQuery.nontable_retrieval I ε snap henc t ht hnt (tableCmd k)
    have hc : (24 : ℝ) ≤ (retrievalCoefficient k : ℝ) := by
      exact_mod_cast (show 24 ≤ retrievalCoefficient k by unfold retrievalCoefficient; omega)
    refine ⟨steps, out, he, hp, hs.trans (mul_le_mul_of_nonneg_right hc ?_)⟩
    unfold multiRetrievalScale
    positivity

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement
open Mission.Structured

def PreprocessingRealization : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ build : Cmd, ∃ B : ℝ, 0 < B ∧
    ∀ (I : MultiInstance k) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ s n, Run (multiInput I ε) build initialStore s n ∧
        (n : ℝ) ≤ B * multiScale I ε ∧ EncodesMultiOutput I ε (s.at 0)

theorem machine_of_preprocessing (hb : PreprocessingRealization) : MachineRealization := by
  intro k hk
  obtain ⟨build, B, hB, hbuild⟩ := hb k hk
  let D := SpaceRAM.reserveCoefficient k
  let Q : ℝ := TableQuery.retrievalCoefficient k
  have hD : 0 ≤ D := by unfold D SpaceRAM.reserveCoefficient; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨(Cmd.seq build (SpaceRAM.cmd k)).program, (TableQuery.queryCmd k).program, B + D + 1 + Q,
    by linarith only [hB, hD, hQ], ?_⟩
  intro I ε hε hε1
  obtain ⟨s, n, hrun, hn, henc⟩ := hbuild I ε hε hε1
  obtain ⟨v, c, htail, hve, hvs, hc⟩ := SpaceRAM.reserve_run I ε hε (multiInput I ε) s henc
  have hcb := SpaceRAM.reserve_bound I (by omega) ε hε hε1 c hc
  obtain ⟨steps, snap, he, hs, hout⟩ := compiled_preprocessing (Run.seq hrun htail)
  have hnm : snap.nm = (v.at 0).nm := congrArg Store.nm hout
  have hrm : snap.rm = (v.at 0).rm := congrArg Store.rm hout
  have hse := TableQuery.preserves_encoding I ε (v.at 0) snap hve (fun j _ => congrFun hnm j) hrm
  have hss : TableQuery.QuerySpace I ε snap := fun r A h => (hvs r A h).trans_eq (congrFun hnm 6).symm
  refine ⟨steps, snap, he, ?_, hse, ?_⟩
  · have hsum : (steps : ℝ) ≤ (n : ℝ) + c + 1 := by exact_mod_cast hs
    have h1 := SpaceRAM.scale_one I (by omega) ε hε hε1
    have hqpos := mul_nonneg hQ (show 0 ≤ multiScale I ε by linarith only [h1])
    change (c : ℝ) ≤ D * multiScale I ε at hcb
    linarith only [hsum, hn, hcb, h1, hqpos]
  · intro t ht
    obtain ⟨l, out, hx, hp, hl⟩ := TableQuery.compiled_retrieval I (by omega) ε hε snap hse hss t ht
    refine ⟨l, out, hx, hp, hl.trans (mul_le_mul_of_nonneg_right ?_ ?_)⟩
    · change Q ≤ B + D + 1 + Q
      linarith only [hB, hD]
    · unfold multiRetrievalScale
      positivity

theorem goal_of_preprocessing (h : PreprocessingRealization) : MultiResourceGoal :=
  goal_of_machineRealization (machine_of_preprocessing h)

end NearLinearRSP.TwoResources.Supplement

end

open NearLinearRSP.TwoResources NearLinearRSP.TwoResources.Supplement

theorem solution :
    ∀ k : ℕ, 2 ≤ k →
      ∃ preprocessing retrieval : Program, ∃ K : ℝ, 0 < K ∧
        ∀ (I : MultiInstance k) (ε : ℝ), 0 < ε → ε < 1 →
          ∃ (steps : ℕ) (snapshot : RAMState),
            Execution preprocessing (multiInput I ε) initialState snapshot steps ∧
            (steps : ℝ) ≤ K * multiScale I ε ∧ EncodesMultiOutput I ε snapshot ∧
            ∀ t : ℕ, t < I.graph.n →
              multiDistance snapshot t = selectedDistance I ε t ∧
              (∃ (querySteps : ℕ) (out : RAMState),
                Execution retrieval (multiInput I ε) (multiQueryStart snapshot t) out querySteps ∧
                multiQueryPath out = selectedPath I ε t ∧
                (querySteps : ℝ) ≤ K * multiRetrievalScale k ε (selectedPath I ε t)) ∧
              (∀ d : ℝ, multiDistance snapshot t = some d →
                ∃ P : List ℕ, selectedPath I ε t = some P ∧
                  RelaxedPath I ε t P ∧ pathWeight I.length P ≤ d ∧
                  ∀ R : List ℕ, ExactFeasible I t R → d ≤ (1 + ε) * pathWeight I.length R) ∧
              ((∃ R : List ℕ, ExactFeasible I t R) →
                (multiDistance snapshot t).isSome = true) ∧
              (∀ P : List ℕ, selectedPath I ε t = some P → RelaxedPath I ε t P) :=
  goal_of_preprocessing bounded_ram_preprocessing
