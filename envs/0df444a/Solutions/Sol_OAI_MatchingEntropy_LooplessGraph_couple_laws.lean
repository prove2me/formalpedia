-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.couple_laws
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:50:24.925533+00:00
-- url     : https://prove2.me/submissions/1e9ef937-27e7-4b2c-8417-878d4302b728

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Contraction.lean:L264-L302
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.couple_laws. The node keeps its source
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
import Theorems.Thm_OAI_MatchingEntropy_jointLaw_first

-- ---- from OAI.Combinatorics.PerfectMatching.Coupling ----
namespace OAI

/-!
Finite pushforwards and couplings with a prescribed common marginal.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

theorem fiberMass_nonneg {A C : Type*} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (c : C) :
    0 ≤ fiberMass p f c := by
  apply Finset.sum_nonneg
  intro a _
  split <;> simp_all

theorem le_fiberMass_self {A C : Type*} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (a : A) :
    p a ≤ fiberMass p f (f a) := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b => if f b = f a then p b else 0)
    (by intro b _; split <;> simp_all) (Finset.mem_univ a)
  simpa only [fiberMass, ite_true] using h

theorem jointLaw_nonneg {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (z : A × B) : 0 ≤ jointLaw p q f g z := by
  unfold jointLaw
  split
  · exact div_nonneg (mul_nonneg (hp _) (hq _)) (fiberMass_nonneg hp f _)
  · rfl

theorem jointLaw_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (b : B) : (∑ a, jointLaw p q f g (a,b)) = q b := by
  have heq : ∀ a, jointLaw p q f g (a,b) =
      (q b / fiberMass q g (g b)) * (if f a=g b then p a else 0) := by
    intro a
    by_cases h : f a=g b
    · simp only [jointLaw, h, ite_true, ← hcompat]
      ring
    · simp [jointLaw, h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change q b / fiberMass q g (g b) * fiberMass p f (g b) = q b
  rw [hcompat]
  by_cases hz : fiberMass q g (g b) = 0
  · have hb : q b = 0 := le_antisymm (by simpa [hz] using le_fiberMass_self hq g b) (hq b)
    simp [hb]
  · exact div_mul_cancel₀ _ hz

theorem jointLaw_mem_simplex {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : p ∈ probabilitySimplex A) (hq : q ∈ probabilitySimplex B)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c) :
    jointLaw p q f g ∈ probabilitySimplex (A × B) := by
  refine ⟨jointLaw_nonneg hp.1 hq.1 f g, ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [jointLaw_first hp.1 f g hcompat]
  exact hp.2

theorem sum_subtype_supported {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P]
    (w : A → ℝ) (hsupp : ∀ a, ¬P a → w a = 0) :
    (∑ a : {a // P a}, w a.val) = ∑ a, w a := by
  have hh : (∑ a : {a // ¬P a}, w a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hsupp a.val a.property
  simpa only [hh, add_zero] using (Fintype.sum_subtype_add_sum_subtype P w)

/-- No mass is lost in retaining only compatible pairs. -/
theorem compatible_jointLaw_mem_simplex {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : p ∈ probabilitySimplex A) (hq : q ∈ probabilitySimplex B)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c) :
    (fun z : {z : A × B // f z.1=g z.2} => jointLaw p q f g z.val) ∈
      probabilitySimplex {z : A × B // f z.1=g z.2} := by
  refine ⟨fun z => jointLaw_nonneg hp.1 hq.1 f g z.val, ?_⟩
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2) (jointLaw p q f g)
    (by intro z hz; simp [jointLaw, hz])]
  exact (jointLaw_mem_simplex hp hq f g hcompat).2

theorem fiberMass_sum {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) : ∑ c, fiberMass p f c = ∑ a, p a := by
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

theorem fiberMass_expect {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (h : C → ℝ) :
    ∑ c, fiberMass p f c * h c = ∑ a, p a*h (f a) := by
  unfold fiberMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem fiberMass_mem_simplex {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (f : A → C) :
    fiberMass p f ∈ probabilitySimplex C :=
  ⟨fiberMass_nonneg hp.1 f, (fiberMass_sum p f).trans hp.2⟩

theorem jointLaw_expect_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : A → ℝ) : ∑ z : A × B, jointLaw p q f g z * h z.1 = ∑ a, p a*h a := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, jointLaw_first hp f g hcompat]

theorem jointLaw_expect_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : B → ℝ) : ∑ z : A × B, jointLaw p q f g z * h z.2 = ∑ b, q b*h b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, jointLaw_second hq f g hcompat]

theorem compatible_jointLaw_expect_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : A → ℝ) :
    ∑ z : {z : A × B // f z.1=g z.2}, jointLaw p q f g z.val * h z.val.1 = ∑ a, p a*h a := by
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2)
    (fun z => jointLaw p q f g z * h z.1)
    (by intro z hz; simp [jointLaw, hz])]
  exact jointLaw_expect_first hp f g hcompat h

theorem compatible_jointLaw_expect_second {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : B → ℝ) :
    ∑ z : {z : A × B // f z.1=g z.2}, jointLaw p q f g z.val * h z.val.2 = ∑ b, q b*h b := by
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2)
    (fun z => jointLaw p q f g z * h z.2)
    (by intro z hz; simp [jointLaw, hz])]
  exact jointLaw_expect_second hq f g hcompat h

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Contraction of tight odd cuts and gluing of perfect matchings and their laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_crosses (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.Crosses S (G.boundaryEdge S M).val :=
  (G.onSide_incident_none S _).mp (Classical.choose_spec (M.property none)).1.2

omit [Fintype E] in
theorem indicator_glue_left (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide S).indicator z.val.1 e := by
  simp only [indicator, glueMatching, G.mem_glued_left S z.val.1 z.val.2 z.property e]

omit [Fintype E] in
theorem indicator_glue_right (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide Sᶜ).indicator z.val.2 e := by
  simp only [indicator, glueMatching, G.mem_glued_right S z.val.1 z.val.2 z.property e]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundary_eq_iff_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) : (G.boundaryEdge S M).val=e.val ↔ e ∈ M.val := by
  constructor
  · intro h
    have he : G.boundaryEdge S M = e := Subtype.ext h
    exact he ▸ G.boundaryEdge_mem S M
  · intro h
    exact (congrArg Subtype.val (G.eq_boundaryEdge S M h hc)).symm

omit [Fintype V] in
theorem boundary_fiber (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e.val = (G.onSide S).mean p e := by
  unfold fiberMass mean
  apply Finset.sum_congr rfl
  intro M _
  simp only [G.boundary_eq_iff_mem S M e hc, indicator]
  split <;> simp

omit [Fintype V] in
theorem boundary_fiber_zero (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : E) (hc : ¬G.Crosses S e) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e = 0 := by
  apply Finset.sum_eq_zero
  intro M _
  have he : (G.boundaryEdge S M).val ≠ e := by
    intro h
    exact hc (h ▸ G.boundaryEdge_crosses S M)
  simp [he]

/-- Exact coupling across a cut, for multigraphs with distinct edge identities. -/
theorem couple_laws (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ)
    {p : (G.onSide S).Matching → ℝ} {q : (G.onSide Sᶜ).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (G.onSide S).Matching)
    (hq : q ∈ probabilitySimplex (G.onSide Sᶜ).Matching)
    (hpx : ∀ e, (G.onSide S).mean p e = x e.val)
    (hqx : ∀ e, (G.onSide Sᶜ).mean q e = x e.val) :
    ∃ r, r ∈ G.feasibleLaws x := by
  let f := fun M : (G.onSide S).Matching => (G.boundaryEdge S M).val
  let g := fun M : (G.onSide Sᶜ).Matching => (G.boundaryEdge Sᶜ M).val
  have hc : ∀ e, fiberMass p f e = fiberMass q g e := by
    intro e
    by_cases he : G.Crosses S e
    · have hk : G.left e ∈ S ∨ G.right e ∈ S := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      have he' := (G.crosses_compl S e).mpr he
      have hk' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := he'.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      rw [G.boundary_fiber S p ⟨e,hk⟩ he, G.boundary_fiber Sᶜ q ⟨e,hk'⟩ he', hpx, hqx]
    · have he' : ¬G.Crosses Sᶜ e := fun h => he ((G.crosses_compl S e).mp h)
      rw [G.boundary_fiber_zero S p e he, G.boundary_fiber_zero Sᶜ q e he']
  let Z := {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching // f z.1=g z.2}
  let w : Z → ℝ := fun z => jointLaw p q f g z.val
  have hw : w ∈ probabilitySimplex Z := compatible_jointLaw_mem_simplex hp hq f g hc
  refine ⟨fiberMass w (G.glueMatching S), fiberMass_mem_simplex hw _, ?_⟩
  ext e
  rw [mean, fiberMass_expect]
  by_cases he : G.left e ∈ S ∨ G.right e ∈ S
  · have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide S).indicator z.val.1 ⟨e,he⟩ := fun z => G.indicator_glue_left S z ⟨e,he⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_first hp.1 f g hc
      (fun M => (G.onSide S).indicator M ⟨e,he⟩)).trans (hpx ⟨e,he⟩)
  · have he' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := by
      simp only [not_or] at he
      exact Or.inl (Finset.mem_compl.mpr he.1)
    have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide Sᶜ).indicator z.val.2 ⟨e,he'⟩ := fun z => G.indicator_glue_right S z ⟨e,he'⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_second hq.1 f g hc
      (fun M => (G.onSide Sᶜ).indicator M ⟨e,he'⟩)).trans (hqx ⟨e,he'⟩)

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ)
    {p : (G.onSide S).Matching → ℝ} {q : (G.onSide Sᶜ).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (G.onSide S).Matching)
    (hq : q ∈ probabilitySimplex (G.onSide Sᶜ).Matching)
    (hpx : ∀ e, (G.onSide S).mean p e = x e.val)
    (hqx : ∀ e, (G.onSide Sᶜ).mean q e = x e.val) :
    ∃ r, r ∈ G.feasibleLaws x := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.couple_laws G S x hp hq hpx hqx
    | exact OAI.MatchingEntropy.LooplessGraph.couple_laws
    | (apply OAI.MatchingEntropy.LooplessGraph.couple_laws <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.couple_laws <;> assumption)
