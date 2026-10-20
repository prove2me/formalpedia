-- Prove2me | solution 1 for OAI.TriangleFace198.expansion_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:53:52.377975+00:00
-- url     : https://prove2.me/submissions/8f584d43-971a-4a12-8e2e-67d1c722e340

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TriangleFace/MatchingImage.lean:L48-L66
-- (upload_full_project.md Phase 4): solution for node OAI.TriangleFace198.expansion_image_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_FractionalReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Components
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_TriangleExpansion

-- ---- from OAI.Combinatorics.MatchingEntropy.Coupling ----
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem fiberMass_nonneg {A : Type uA} {C : Type uC} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (c : C) :
    0 ≤ fiberMass p f c := by
  apply Finset.sum_nonneg
  intro a _
  split <;> simp_all

theorem fiberMass_sum {A : Type uA} {C : Type uC} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) : ∑ c, fiberMass p f c = ∑ a, p a := by
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

theorem fiberMass_expect {A : Type uA} {C : Type uC} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (h : C → ℝ) :
    ∑ c, fiberMass p f c * h c = ∑ a, p a*h (f a) := by
  unfold fiberMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem fiberMass_mem_simplex {A : Type uA} {C : Type uC} [Fintype A] [Fintype C] [DecidableEq C]
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (f : A → C) :
    fiberMass p f ∈ probabilitySimplex C :=
  ⟨fiberMass_nonneg hp.1 f, (fiberMass_sum p f).trans hp.2⟩

end MatchingEntropyBounds

end

end OAI

-- ---- from OAI.Combinatorics.MatchingEntropy.FractionalReduction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem fiberMass_injective_apply {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f) (a : A) :
    fiberMass p f (f a) = p a := by
  classical
  simp [fiberMass, hf.eq_iff]

theorem fiberMass_outside {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (b : B) (hb : b ∉ Set.range f) : fiberMass p f b = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  exact ite_eq_right (fun h => hb ⟨a,h⟩)

theorem fiberMass_pullback {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : B → ℝ) (f : A → B) (hf : Function.Injective f)
    (hp : ∀ b, b ∉ Set.range f → p b = 0) :
    fiberMass (fun a => p (f a)) f = p := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hb
    exact fiberMass_injective_apply _ _ hf a
  · rw [fiberMass_outside _ _ _ hb, hp b hb]

theorem simplex_of_fiberMass {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f)
    (hp : fiberMass p f ∈ probabilitySimplex B) : p ∈ probabilitySimplex A := by
  refine ⟨fun a => ?_, ?_⟩
  · simpa only [fiberMass_injective_apply p f hf] using hp.1 (f a)
  · rw [← fiberMass_sum p f]
    exact hp.2

section AffineFaces
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]

end AffineFaces

section FaceMaps
variable {W : Type uW} {D : Type uD} [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D]

end FaceMaps

end MatchingEntropyBounds.Refined

end

end OAI

-- ---- from OAI.Combinatorics.MatchingEntropy.TriangleExpansion ----
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

section TriangleExpansion
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

end TriangleExpansion

section ExpansionSupport
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem triangleVertices_eq (v : V) :
    triangleVertices v = {Sum.inl v, Sum.inr 0, Sum.inr 1} := by
  simp [triangleVertices,Fin.univ_succ,triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem mem_triangleVertices_tip (v : V) (i : Fin 3) : triangleTip v i ∈ triangleVertices v :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_mem_triangle (v w : V) (i : Fin 3) :
    reattach v i w ∈ triangleVertices v ↔ w = v := by
  by_cases h : w = v
  · simp [reattach,h,mem_triangleVertices_tip]
  · simp [reattach,h,triangleVertices_eq]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_crosses_old (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (e : E) :
    (triangleExpansion G c v).Crosses (triangleVertices v) (Sum.inl e) ↔ G.Incident v e := by
  have hl := G.loopless e
  simp only [LooplessGraph.Crosses,triangleExpansion,Sum.elim_inl,reattach_mem_triangle,
    LooplessGraph.Incident]
  constructor
  · tauto
  · rintro (h | h)
    · exact Or.inl ⟨h,fun hh => hl (h.trans hh.symm)⟩
    · exact Or.inr ⟨fun hh => hl (hh.trans h.symm),h⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_crosses_new (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (i : Fin 3) :
    ¬(triangleExpansion G c v).Crosses (triangleVertices v) (Sum.inr i) := by
  simp [LooplessGraph.Crosses,triangleExpansion,mem_triangleVertices_tip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem triangleVertices_odd (v : V) : Odd (triangleVertices v).card := by
  have hcard : (triangleVertices v).card = 3 := by
    rw [triangleVertices,Finset.card_image_of_injective _ (triangleTip_injective v)]
    simp
  rw [hcard]
  norm_num

omit [Fintype V] [DecidableEq E] in
theorem expanded_cutMass (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (y : E ⊕ Fin 3 → ℝ) :
    (triangleExpansion G c v).cutMass y (triangleVertices v) = G.degree (fun e => y (Sum.inl e)) v := by
  simp only [LooplessGraph.cutMass,LooplessGraph.cut,Finset.sum_filter,Fintype.sum_sum_type,
    expanded_crosses_old,expanded_crosses_new,ite_false,Finset.sum_const_zero,add_zero,
    LooplessGraph.degree]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expandMatching_injective (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    Function.Injective (expandMatching G c v) := by
  intro M N h
  apply Subtype.ext
  ext e
  have hh := congrArg (fun K : (triangleExpansion G c v).Matching => Sum.inl e ∈ K.val) h
  simpa [expandMatching,expandEdges] using hh

omit [Fintype V] in
theorem cutMass_indicator_card (G : LooplessGraph V E) (M : G.Matching) (S : Finset V) :
    G.cutMass (G.indicator M) S = ((M.val.filter (G.Crosses S)).card : ℝ) := by
  simp only [LooplessGraph.cutMass,LooplessGraph.indicator,Finset.sum_boole]
  congr 2
  ext e
  simp [LooplessGraph.cut,and_comm]

omit [Fintype V] in
theorem crossOnce_of_cut_eq_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching)
    (hN : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).indicator N) (triangleVertices v) = 1) :
    CrossOnce G c v N := by
  rw [cutMass_indicator_card] at hN
  have hn : (N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v))).card = 1 := by
    exact_mod_cast hN
  obtain ⟨f,hf⟩ := Finset.card_eq_one.mp hn
  have hfm : f ∈ N.val ∧ (triangleExpansion G c v).Crosses (triangleVertices v) f := by
    have hh : f ∈ N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v)) := by rw [hf]; simp
    exact Finset.mem_filter.mp hh
  rcases f with e | i
  · refine ⟨e,⟨hfm.1,(expanded_crosses_old G c v e).mp hfm.2⟩,?_⟩
    intro f hfg
    have hh : Sum.inl f ∈ N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v)) :=
      Finset.mem_filter.mpr ⟨hfg.1,(expanded_crosses_old G c v f).mpr hfg.2⟩
    rw [hf,Finset.mem_singleton] at hh
    exact Sum.inl.inj hh
  · exact (expanded_crosses_new G c v i hfm.2).elim

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem fin3_add_one_ne (i : Fin 3) : i + 1 ≠ i := by fin_cases i <;> decide

omit [Fintype V] in
theorem expand_contract (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    expandMatching G c v (contractMatching G c v N hN) = N := by
  let M := contractMatching G c v N hN
  let e := incidentChoice G M v
  have he : Sum.inl e ∈ N.val ∧ G.Incident v e := by
    simpa [e,M,contractMatching,contractEdges] using incidentChoice_spec G M v
  have hcol : ∀ i : Fin 3, Sum.inr i ∈ N.val → i = c e := by
    intro i hi
    by_contra hn
    have hh := (N.property (triangleTip v (c e))).unique
      ⟨hi,(expanded_incident_new_tip G c v i (c e)).mpr hn⟩
      ⟨he.1,(expanded_incident_old_tip G c v e (c e)).mpr ⟨he.2,rfl⟩⟩
    cases hh
  have hmem : Sum.inr (c e) ∈ N.val := by
    obtain ⟨f,hf,_⟩ := N.property (triangleTip v (c e + 1))
    rcases f with f | i
    · have hfv := (expanded_incident_old_tip G c v f (c e + 1)).mp hf.2
      have hfe : f = e := hN.unique ⟨hf.1,hfv.1⟩ he
      have hh : c e = c e + 1 := hfe ▸ hfv.2
      exact (fin3_add_one_ne (c e) hh.symm).elim
    · exact hcol i hf.1 ▸ hf.1
  apply Subtype.ext
  ext f
  rcases f with f | i
  · simp [expandMatching,expandEdges,contractMatching,contractEdges]
  · simp only [expandMatching,expandEdges,Finset.inr_mem_disjSum,Finset.mem_singleton]
    change i = c e ↔ Sum.inr i ∈ N.val
    exact ⟨fun hi => hi ▸ hmem,hcol i⟩

omit [Fintype V] in
theorem range_expandMatching_of_crossOnce (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    N ∈ Set.range (expandMatching G c v) := ⟨contractMatching G c v N hN,expand_contract G c v N hN⟩

omit [Fintype V] in
theorem cutMass_mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (S : Finset V) :
    G.cutMass (G.mean p) S = ∑ M, p M * G.cutMass (G.indicator M) S := by
  simp only [LooplessGraph.cutMass,LooplessGraph.mean,Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype V] in
theorem positive_law_tight_cut (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (S : Finset V) (hS : Odd S.card)
    (ht : G.cutMass (G.mean p) S = 1) {M : G.Matching} (hM : p M ≠ 0) :
    G.cutMass (G.indicator M) S = 1 := by
  have hl (N : G.Matching) : 0 ≤ G.cutMass (G.indicator N) S - 1 :=
    sub_nonneg.mpr ((G.indicator_mem_constraintPolytope N).2.2 S hS)
  have heq : ∑ N, p N * (G.cutMass (G.indicator N) S - 1) = 0 := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,← cutMass_mean,ht,hp.2,sub_self]
  have hz : p M * (G.cutMass (G.indicator M) S - 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun N _ => mul_nonneg (hp.1 N) (hl N))).mp heq M (Finset.mem_univ M)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hM)

omit [Fintype V] in
theorem expanded_pull_simplex (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {p : (triangleExpansion G c v).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (triangleExpansion G c v).Matching)
    (ht : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1) :
    p = fiberMass (fun M => p (expandMatching G c v M)) (expandMatching G c v) ∧
    (fun M => p (expandMatching G c v M)) ∈ probabilitySimplex G.Matching := by
  have heq : fiberMass (fun M => p (expandMatching G c v M)) (expandMatching G c v) = p := by
    apply fiberMass_pullback _ _ (expandMatching_injective G c v)
    intro N hN
    by_contra hn
    exact hN (range_expandMatching_of_crossOnce G c v N (crossOnce_of_cut_eq_one G c v N
      (positive_law_tight_cut _ hp _ (triangleVertices_odd v) ht hn)))
  refine ⟨heq.symm,simplex_of_fiberMass _ _ (expandMatching_injective G c v) ?_⟩
  exact heq.symm ▸ hp

end ExpansionSupport
end MatchingEntropyBounds.Refined

end

end OAI

-- ---- from OAI.Combinatorics.TriangleFace.Labels ----
namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem localEdge_spec (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (i : Fin 3) :
    G.Incident v (localEdge G c v hc i) ∧ c (localEdge G c v hc i) = i :=
  (Classical.choose_spec (hc i)).1

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem eq_localEdge (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) {e : E} {i : Fin 3}
    (he : G.Incident v e) (hi : c e = i) : e = localEdge G c v hc i :=
  (Classical.choose_spec (hc i)).2 e ⟨he,hi⟩

end TriangleFace198
end

end OAI

-- ---- from OAI.Combinatorics.TriangleFace.MatchingImage ----
namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

omit [Fintype V] [Fintype E] in
theorem expandMatching_indicator (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) (M : G.Matching) :
    (triangleExpansion G c v).indicator (expandMatching G c v M) = localExtension G c v hc (G.indicator M) := by
  ext e
  rcases e with e | i
  · simp [LooplessGraph.indicator,expandMatching,expandEdges,localExtension]
  · have hh : c (incidentChoice G M v) = i ↔ localEdge G c v hc i ∈ M.val := by
      constructor
      · intro h
        rw [← eq_localEdge G c v hc (incidentChoice_spec G M v).2 h]
        exact (incidentChoice_spec G M v).1
      · intro h
        rw [← eq_incidentChoice G M v h (localEdge_spec G c v hc i).1]
        exact (localEdge_spec G c v hc i).2
    simp only [LooplessGraph.indicator,expandMatching,expandEdges,Finset.inr_mem_disjSum,
      Finset.mem_singleton,localExtension,LinearMap.coe_mk,AddHom.coe_mk,Sum.elim_inr]
    simp only [eq_comm (a := i) (b := c (incidentChoice G M v)),hh]

theorem expanded_push_mean {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) (q : G.Matching → ℝ) :
    (triangleExpansion G c v).mean (fiberMass q (expandMatching G c v)) =
      localExtension G c v hc (G.mean q) := by
  ext e
  rw [LooplessGraph.mean,fiberMass_expect]
  simp_rw [expandMatching_indicator G c v hc]
  rcases e with e | i <;> rfl

theorem expanded_push_feasible (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) {x : E → ℝ} {q : G.Matching → ℝ}
    (hq : q ∈ G.feasibleLaws x) :
    fiberMass q (expandMatching G c v) ∈ (triangleExpansion G c v).feasibleLaws (localExtension G c v hc x) := by
  exact ⟨fiberMass_mem_simplex hq.1 _,by rw [expanded_push_mean G c v hc,hq.2]⟩

theorem expansion_image_eq (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) :
    localExtension G c v hc '' G.polytope =
      {y | y ∈ (triangleExpansion G c v).polytope ∧
        (triangleExpansion G c v).cutMass y (triangleVertices v) = 1} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨q,hq⟩ := (G.mem_polytope_iff x).mp hx
    refine ⟨((triangleExpansion G c v).mem_polytope_iff _).mpr
      ⟨_,expanded_push_feasible G c v hc hq⟩,?_⟩
    rw [expanded_cutMass]
    exact (G.polytope_subset_constraintPolytope hx).2.1 v
  · rintro ⟨hy,ht⟩
    obtain ⟨p,hp⟩ := ((triangleExpansion G c v).mem_polytope_iff y).mp hy
    have ht' : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1 := hp.2.symm ▸ ht
    obtain ⟨heq,hq⟩ := expanded_pull_simplex G c v hp.1 ht'
    refine ⟨_,G.mean_mem_polytope hq,?_⟩
    rw [← expanded_push_mean,← heq,hp.2]

end TriangleFace198
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangleFace198
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined


theorem solution.{uV,uE} : type_of% @_root_.OAI.TriangleFace198.expansion_image_eq.{uV,uE} := @_root_.OAI.TriangleFace198.expansion_image_eq.{uV,uE}
