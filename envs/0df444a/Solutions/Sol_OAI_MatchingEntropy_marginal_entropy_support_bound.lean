-- Prove2me | solution 1 for OAI.MatchingEntropy.marginal_entropy_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:36:44.747217+00:00
-- url     : https://prove2.me/submissions/59156237-86f9-410e-b3e7-04a4663bd8db

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Main.lean:L49-L82
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.marginal_entropy_support_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance
import Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff

-- ---- from OAI.Combinatorics.PerfectMatching.Entropy ----
namespace OAI

/-!
Finite Shannon entropy and attainment of its supremum over feasible matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem coordinate_mem_Icc (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) (e : E) : y e ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  constructor
  · exact Finset.sum_nonneg (fun M _ ↦ mul_nonneg (hp.1 M) (G.indicator_nonneg M e))
  · calc
      ∑ M, p M * G.indicator M e ≤ ∑ M, p M * 1 :=
        Finset.sum_le_sum (fun M _ ↦ mul_le_mul_of_nonneg_left (G.indicator_le_one M e) (hp.1 M))
      _ = 1 := by simpa using hp.2

omit [Fintype E] [DecidableEq E] in
/-- Counting the two distinct endpoints; parallel identities are never collapsed. -/
theorem incident_vertex_sum (G : LooplessGraph V E) (e : E) :
    (∑ v, if G.Incident v e then (1 : ℕ) else 0) = 2 := by
  classical
  have he (v : V) : (if G.Incident v e then (1 : ℕ) else 0) =
      (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) := by
    by_cases hl : G.left e = v <;> by_cases hr : G.right e = v
    · exact False.elim (G.loopless e (hl.trans hr.symm))
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
  simp_rw [he, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incident_sum (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    (∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0) = 1 := by
  classical
  obtain ⟨e, ⟨he, hv⟩, hu⟩ := M.property v
  rw [Finset.sum_eq_single e]
  · simp [hv]
  · intro e' he' hne
    have hn : ¬ G.Incident v e' := fun hv' ↦ hne (hu e' ⟨he', hv'⟩)
    simp [hn]
  · simp [he]

omit [Fintype E] [DecidableEq E] in
theorem matching_card_twice (G : LooplessGraph V E) (M : G.Matching) :
    2 * M.val.card = Fintype.card V := by
  classical
  calc
    2 * M.val.card = ∑ e ∈ M.val, ∑ v, if G.Incident v e then (1 : ℕ) else 0 := by
      simp_rw [G.incident_vertex_sum]
      simp [Nat.mul_comm]
    _ = ∑ v, ∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by
      simp_rw [G.matching_incident_sum]
      simp

omit [Fintype E] [DecidableEq E] in
theorem matching_card (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) : M.val.card = m := by
  have h := G.matching_card_twice M
  omega

theorem indicator_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) :
    ∑ e, G.indicator M e = (m : ℝ) := by
  simp [indicator, G.matching_card hV M]

/-- All feasible marginal vectors have mass m, as in the entropy proof. -/
theorem marginal_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) {y : E → ℝ} (hy : y ∈ G.polytope) :
    ∑ e, y e = (m : ℝ) := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  simp_rw [mean]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.indicator_sum hV]
  rw [← Finset.sum_mul, hp.2, one_mul]

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.MatchingCovariance ----
namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem sum_positive_support (x f : E → ℝ) (hf : ∀ e, ¬ 0 < x e → f e=0) :
    (∑ e, f e) = ∑ e : {e // 0 < x e}, f e.val := by
  classical
  have hz : (∑ e : {e // ¬ 0 < x e}, f e.val)=0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  have hh := Fintype.sum_subtype_add_sum_subtype (fun e => 0 < x e) f
  rw [hz,add_zero] at hh
  exact hh.symm

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Main ----
namespace OAI

/-!
The nonlinear entropy defect bound
`F - H ≤ 8m (1 - exp (-F/m))` for finite loopless multigraphs on `2m` vertices,
and the perfect matching count bound `[k exp (-8 (1 - 1/k))]^m`,
with its coarse bound `(exp (-8) k)^m`, when the entire edge set
is partitioned into `k ≥ 1` perfect matchings.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Entropy on s positive edge coordinates of total mass m is at most m log(s/m). -/
theorem marginal_entropy_support_bound (G : LooplessGraph V E) {m : ℕ}
    (hm : 0 < m) (hV : Fintype.card V=2*m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ entropy x ∧ 0 < Fintype.card {e // 0 < x e} ∧
      entropy x ≤ (m:ℝ)*Real.log ((Fintype.card {e // 0 < x e}:ℝ)/(m:ℝ)) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hmass := G.marginal_sum hV hx
  have hn : ∀ e, 0 ≤ x e := fun e => (G.coordinate_mem_Icc hx e).1
  have hz : ∀ e, ¬ 0 < x e → x e=0 := fun e he => le_antisymm (le_of_not_gt he) (hn e)
  have hsum : (∑ e : {e // 0 < x e}, x e.val)=(m:ℝ) :=
    (sum_positive_support x x hz).symm.trans hmass
  have hent : entropy (fun e : {e // 0 < x e} => x e.val)=entropy x := by
    unfold entropy
    exact (sum_positive_support x (fun e => Real.negMulLog (x e))
      (fun e he => by rw [hz e he,Real.negMulLog_zero])).symm
  have hpossum : 0 < ∑ e, x e := by rw [hmass]; exact hmR
  obtain ⟨e,_,he⟩ := (Finset.sum_pos_iff_of_nonneg (fun e _ => hn e)).mp hpossum
  have hs : 0 < Fintype.card {e // 0 < x e} := Fintype.card_pos_iff.mpr ⟨⟨e,he⟩⟩
  have hsR : (0:ℝ) < Fintype.card {e // 0 < x e} := by exact_mod_cast hs
  refine ⟨Finset.sum_nonneg (fun e _ => Real.negMulLog_nonneg (hn e) (G.coordinate_mem_Icc hx e).2),hs,?_⟩
  let c : ℝ := (Fintype.card {e // 0 < x e}:ℝ)/(m:ℝ)
  have hc : 0 < c := div_pos hsR hmR
  have hcm : c*(m:ℝ)=Fintype.card {e // 0 < x e} := div_mul_cancel₀ _ hmR.ne'
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun e : {e // 0 < x e} => fun _ =>
    Real.negMulLog_le_one_sub_self (mul_nonneg hc.le e.property.le))
  simp_rw [Real.negMulLog_mul] at hb
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,hsum,
    Finset.sum_sub_distrib,← Finset.mul_sum,hsum] at hb
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hb
  change (m:ℝ)*Real.negMulLog c+c*entropy (fun e : {e // 0 < x e} => x e.val) ≤
    (Fintype.card {e // 0 < x e}:ℝ)-c*(m:ℝ) at hb
  rw [hent,Real.negMulLog,hcm,sub_self] at hb
  change entropy x ≤ (m:ℝ)*Real.log c
  nlinarith

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution (G : LooplessGraph V E) {m : ℕ}
    (hm : 0 < m) (hV : Fintype.card V=2*m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ entropy x ∧ 0 < Fintype.card {e // 0 < x e} ∧
      entropy x ≤ (m:ℝ)*Real.log ((Fintype.card {e // 0 < x e}:ℝ)/(m:ℝ)) := by
  first
    | exact OAI.MatchingEntropy.marginal_entropy_support_bound G hm hV hx
    | exact OAI.MatchingEntropy.marginal_entropy_support_bound
    | (apply OAI.MatchingEntropy.marginal_entropy_support_bound <;> assumption)
    | (intros; apply OAI.MatchingEntropy.marginal_entropy_support_bound <;> assumption)
