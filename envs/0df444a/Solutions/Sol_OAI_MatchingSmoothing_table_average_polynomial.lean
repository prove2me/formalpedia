-- Prove2me | solution 1 for OAI.MatchingSmoothing.table_average_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:32:29.874976+00:00
-- url     : https://prove2.me/submissions/130548db-8d25-41e9-973a-64adb2ea69fd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TablePolynomials.lean:L80-L100
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.table_average_polynomial. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Theorems.Thm_OAI_MatchingSmoothing_Pairing_redundant_edgeMonomial
import Theorems.Thm_OAI_MatchingSmoothing_lowDegree_lift
import Theorems.Thm_OAI_MatchingSmoothing_monomial_candidate_identity
import Theorems.Thm_OAI_MatchingSmoothing_mul_mem_lowDegree
import Theorems.Thm_OAI_MatchingSmoothing_predicateAverage_of_constant
import Theorems.Thm_OAI_MatchingSmoothing_standardPairing_table

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeProducts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

lemma lowDegree_mono (x : E → X → ℝ) {d e : ℕ} (h : d ≤ e) :
    lowDegree x d ≤ lowDegree x e := by
  apply Submodule.span_mono
  rintro f ⟨l, hl, hf⟩
  exact ⟨l, hl.trans h, hf⟩

lemma one_mem_lowDegree (x : E → X → ℝ) (d : ℕ) : (1 : X → ℝ) ∈ lowDegree x d :=
  Submodule.subset_span ⟨[], Nat.zero_le _, rfl⟩

lemma coord_mem_lowDegree (x : E → X → ℝ) (e : E) : x e ∈ lowDegree x 1 := by
  apply Submodule.subset_span
  exact ⟨[e], by simp, by simp⟩

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Pairings ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
namespace Pairing
variable {α : Type u_2}

lemma cycleType_eq [Fintype α] [DecidableEq α] (M N : Pairing α) :
    M.1.cycleType = N.1.cycleType := by
  have hm := Equiv.Perm.cycleType_of_pow_prime_eq_one M.partner_sq
  have hn := Equiv.Perm.cycleType_of_pow_prime_eq_one N.partner_sq
  have hsum (P : Pairing α) : P.1.cycleType.sum = Fintype.card α := by
    rw [Equiv.Perm.sum_cycleType]
    have hs : P.1.support = Finset.univ := by
      ext a
      simp [Equiv.Perm.mem_support, P.partner_ne]
    rw [hs, Finset.card_univ]
  have hc : M.1.cycleType.card = N.1.cycleType.card := by
    have he := (hsum M).trans (hsum N).symm
    rw [hm, hn] at he
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at he
    omega
  rw [hm, hn, hc]

lemma exists_relabel [Fintype α] [DecidableEq α] (M N : Pairing α) :
    ∃ p : Equiv.Perm α, relabel p M = N := by
  have h := Equiv.Perm.isConj_iff_cycleType_eq.mpr (cycleType_eq M N)
  rcases isConj_iff.mp h with ⟨p, hp⟩
  refine ⟨p, Subtype.ext ?_⟩
  exact hp

end Pairing
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TableMoments ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma histogram_cast_sum {V : Type u_4} {T : Type u_5} [Fintype V] [DecidableEq T] (f : V → T) (t : T) :
    (histogram f t : ℝ) = ∑ i, if f i = t then 1 else 0 := by
  classical
  simp only [histogram, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

end ThreeTableMoment
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingIncidence ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma table_relabel (p : Equiv.Perm V) (M : Pairing V) (f : V → Fin 3) :
    (relabel p M).table f = M.table (f ∘ p) := by
  funext t
  unfold table
  congr 1
  have he : (fun v => threeEdgeType (f v, f ((relabel p M).1 v))) ∘ p =
      (fun v => threeEdgeType ((f ∘ p) v, (f ∘ p) (M.1 v))) := by
    funext v
    simp only [Function.comp_apply, relabel_apply]
    rw [Equiv.Perm.inv_def, p.symm_apply_apply]
  rw [← he, histogram_comp_perm]

end Pairing

section StandardTable
variable {H : Type u_2} [Fintype H] [DecidableEq H]

end StandardTable

section MatchingIncidence
variable {H : Type u_3} [Fintype H] [DecidableEq H]

end MatchingIncidence
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.EquivariantCompression ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
namespace Pairing
variable {V : Type u_1}

lemma act_pointwise_mul (p : Equiv.Perm V) (f g : Pairing V → ℝ) :
    act p (f * g) = act p f * act p g := rfl

lemma act_edgeCoord (p : Equiv.Perm V) (e : V × V) :
    act p (edgeCoord e) = edgeCoord (p e.1, p e.2) := by
  classical
  ext M
  simp only [act_apply, edgeCoord, relabel_apply, inv_inv]
  congr 1
  exact propext p.symm_apply_eq

end Pairing

open scoped RealInnerProductSpace
section EuclideanPermutations
variable {X : Type u_2} [Fintype X]

end EuclideanPermutations

section CompressionEquivariance
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end CompressionEquivariance
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeMonomials ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
namespace Pairing
variable {V : Type u_1}

lemma mem_edgeSupport (l : List (V × V)) (v : V) :
    v ∈ edgeSupport l ↔ ∃ e ∈ l, v = e.1 ∨ v = e.2 := by
  simp only [edgeSupport, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, he, Or.inl rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
  · rintro ⟨e, he, h | h⟩
    · exact Or.inl ⟨e, he, h.symm⟩
    · exact Or.inr ⟨e, he, h.symm⟩

lemma edgeMonomial_eq_indicator (l : List (V × V)) (M : Pairing V) :
    edgeMonomial l M = if ContainsList M l then 1 else 0 := by
  induction l with
  | nil => simp [edgeMonomial, ContainsList]
  | cons e l ih =>
    simp only [edgeMonomial, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih]
    simp only [ContainsList, List.mem_cons, forall_eq_or_imp, edgeCoord]
    split_ifs <;> simp_all

lemma edgeMonomial_cons (e : V × V) (l : List (V × V)) :
    edgeMonomial (e::l) = edgeCoord e * edgeMonomial l := by
  simp [edgeMonomial]

lemma edgeMonomial_zero_of_unsatisfiable (l : List (V × V))
    (h : ¬ ∃ M : Pairing V, ContainsList M l) : edgeMonomial l = 0 := by
  funext M
  rw [edgeMonomial_eq_indicator, ite_eq_right (fun hm => h ⟨M, hm⟩)]
  rfl

lemma edgeMonomial_act_fix (l : List (V × V)) (p : Equiv.Perm V)
    (hp : ∀ v ∈ edgeSupport l, p v = v) : act p (edgeMonomial l) = edgeMonomial l := by
  funext M
  simp only [act_apply, edgeMonomial_eq_indicator]
  congr 1
  apply propext
  apply forall₂_congr
  intro e he
  have h₁ := hp e.1 ((mem_edgeSupport l e.1).mpr ⟨e, he, Or.inl rfl⟩)
  have h₂ := hp e.2 ((mem_edgeSupport l e.2).mpr ⟨e, he, Or.inr rfl⟩)
  simp only [relabel_apply, inv_inv]
  rw [h₁, Equiv.Perm.inv_def, p.symm_apply_eq, h₂]

end Pairing

section ColorAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

lemma colorAverage_apply (z : V → C) (f : Pairing V → ℝ) (M : Pairing V) :
    colorAverage z f M =
      (∑ p : colorStabilizer z, Pairing.act p.1 f M) / Fintype.card (colorStabilizer z) := by
  simp [colorAverage, div_eq_mul_inv, mul_comm]

lemma colorAverage_act (z : V → C) (q : colorStabilizer z) (f : Pairing V → ℝ) :
    colorAverage z (Pairing.act q.1 f) = colorAverage z f := by
  funext M
  simp only [colorAverage_apply, ← Pairing.act_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight q) (fun p : colorStabilizer z => Pairing.act p.1 f M)

lemma colorAverage_one (z : V → C) : colorAverage z (1 : Pairing V → ℝ) = 1 := by
  funext M
  simp [colorAverage_apply, Pairing.act_apply, Fintype.card_ne_zero]

lemma colorAverage_mul_invariant (z : V → C) (f g : Pairing V → ℝ)
    (hf : ∀ p : colorStabilizer z, Pairing.act p.1 f = f) :
    colorAverage z (f*g) = f * colorAverage z g := by
  funext M
  simp only [colorAverage_apply, Pi.mul_apply, Pairing.act_apply]
  have h (p : colorStabilizer z) : f (Pairing.relabel p.1⁻¹ M) = f M := congrFun (hf p) M
  simp_rw [h, ← Finset.mul_sum, mul_div_assoc]

end ColorAverage
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PartialColorings ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorCounting
variable {V : Type u_1} {C : Type u_2} [Fintype V]

omit [Fintype V] in
lemma swap_preserves_color (z : V → C) {a b : V} (hab : z a = z b) (v : V) :
    z (Equiv.swap a b v) = z v := by
  by_cases hva : v = a
  · subst v; simpa using hab.symm
  by_cases hvb : v = b
  · subst v; simpa using hab
  rw [Equiv.swap_apply_of_ne_of_ne hva hvb]

omit [Fintype V] in
lemma swap_fixes_finset (U : Finset V) {a b : V} (ha : a ∉ U) (hb : b ∉ U)
    (v : V) (hv : v ∈ U) : Equiv.swap a b v = v :=
  Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hv)) (fun h => hb (h ▸ hv))

omit [Fintype V] in
lemma exists_color_perm_fixing_pair (z : V → C) (U : Finset V)
    {a b c d : V} (ha : a ∉ U) (hb : b ∉ U) (hc : c ∉ U) (hd : d ∉ U)
    (hab : a ≠ b) (hcd : c ≠ d) (hzac : z a = z c) (hzbd : z b = z d) :
    ∃ p : colorStabilizer z, (∀ v ∈ U, p.1 v = v) ∧ p.1 a = c ∧ p.1 b = d := by
  let q := Equiv.swap a c
  have hq : ∀ v, z (q v) = z v := swap_preserves_color z hzac
  have hqfix : ∀ v ∈ U, q v = v := swap_fixes_finset U ha hc
  have hqb : q b ∉ U := by
    intro h
    have hh := hqfix (q b) h
    have : b = q b := by simpa only [q, Equiv.swap_apply_self] using hh
    exact hb (this ▸ h)
  let p := Equiv.swap (q b) d * q
  have hp : p ∈ colorStabilizer z := by
    intro v
    change z (Equiv.swap (q b) d (q v)) = z v
    rw [swap_preserves_color z ((hq b).trans hzbd), hq]
  refine ⟨⟨p, hp⟩, ?_, ?_, ?_⟩
  · intro v hv
    change Equiv.swap (q b) d (q v) = v
    rw [hqfix v hv, swap_fixes_finset U hqb hd v hv]
  · change Equiv.swap (q b) d (q a) = c
    have hqbc : q b ≠ c := by
      change Equiv.swap a c b ≠ c
      intro h
      have hh := congrArg (Equiv.swap a c) h
      have : b = a := by simpa using hh
      exact hab this.symm
    rw [show q a = c by simp [q]]
    exact Equiv.swap_apply_of_ne_of_ne hqbc.symm hcd
  · change Equiv.swap (q b) d (q b) = d
    simp

lemma tableCoordinate_invariant (z : V → C) (c : C × C) (p : colorStabilizer z) :
    Pairing.act p.1 (tableCoordinate z c) = tableCoordinate z c := by
  funext M
  simp only [Pairing.act_apply, tableCoordinate, Pairing.relabel_apply, inv_inv]
  have hi (v : V) : z (p.1⁻¹ v) = z v := (p⁻¹).property v
  simp_rw [hi]
  rw [← Equiv.sum_comp p.1 (fun v => if z v = c.1 ∧ z (M.1 v) = c.2 then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro v _
  rw [p.property]

lemma mem_candidateEdges (z : V → C) (U : Finset V) (c : C × C) (e : V × V) :
    e ∈ candidateEdges z U c ↔
      e.1 ∉ U ∧ e.2 ∉ U ∧ e.1 ≠ e.2 ∧ z e.1 = c.1 ∧ z e.2 = c.2 := by
  simp [candidateEdges]

lemma candidate_average_eq (z : V → C) (l : List (V × V)) (c : C × C)
    (e f : V × V) (he : e ∈ candidateEdges z (Pairing.edgeSupport l) c)
    (hf : f ∈ candidateEdges z (Pairing.edgeSupport l) c) :
    colorAverage z (Pairing.edgeMonomial (e::l)) =
      colorAverage z (Pairing.edgeMonomial (f::l)) := by
  obtain ⟨ha, hb, hab, hza, hzb⟩ := (mem_candidateEdges _ _ _ _).mp he
  obtain ⟨hc, hd, hcd, hzc, hzd⟩ := (mem_candidateEdges _ _ _ _).mp hf
  obtain ⟨p, hp, hpa, hpb⟩ := exists_color_perm_fixing_pair z (Pairing.edgeSupport l)
    ha hb hc hd hab hcd (hza.trans hzc.symm) (hzb.trans hzd.symm)
  rw [← colorAverage_act z p (Pairing.edgeMonomial (e::l)), Pairing.edgeMonomial_cons]
  have hact : Pairing.act p.1 (Pairing.edgeCoord e * Pairing.edgeMonomial l) =
      Pairing.edgeCoord f * Pairing.edgeMonomial l := by
    rw [Pairing.act_pointwise_mul, Pairing.edgeMonomial_act_fix l p.1 hp,
      Pairing.act_edgeCoord, hpa, hpb]
  rw [hact, Pairing.edgeMonomial_cons]

end ColorCounting
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.ColorPolynomials ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorPolynomials
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma colorAverage_recurrence (z : V → C) (l : List (V × V)) (e : V × V)
    (he : e ∈ candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2))
    (M₀ : Pairing V) (h₀ : Pairing.ContainsList M₀ l) :
    ((candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)).card : ℝ) •
      colorAverage z (Pairing.edgeMonomial (e::l)) =
    (tableCoordinate z (z e.1,z e.2) -
      (∑ v ∈ Pairing.edgeSupport l,
        if z v = z e.1 ∧ z (M₀.1 v) = z e.2 then (1:ℝ) else 0) • 1) *
      colorAverage z (Pairing.edgeMonomial l) := by
  let S := candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)
  have hsum : (∑ f ∈ S, colorAverage z (Pairing.edgeMonomial (f::l))) =
      ((S.card : ℕ) : ℝ) • colorAverage z (Pairing.edgeMonomial (e::l)) := by
    calc
      _ = ∑ _f ∈ S, colorAverage z (Pairing.edgeMonomial (e::l)) := by
        apply Finset.sum_congr rfl
        intro f hf
        exact candidate_average_eq z l _ f e hf he
      _ = _ := by
        funext M
        simp [Pi.smul_apply]
  have hm : (∑ f ∈ S, Pairing.edgeMonomial (f::l)) =
      Pairing.edgeMonomial l * ∑ f ∈ S, Pairing.edgeCoord f := by
    simp only [Pairing.edgeMonomial_cons, ← Finset.sum_mul, mul_comm]
  rw [← hsum, ← map_sum, hm, monomial_candidate_identity z l _ M₀ h₀, mul_comm]
  apply colorAverage_mul_invariant
  intro p
  rw [map_sub, tableCoordinate_invariant, map_smul]
  rfl

lemma colorAverage_monomial_mem (z : V → C) (l : List (V × V)) :
    colorAverage z (Pairing.edgeMonomial l) ∈ lowDegree (tableCoordinate z) l.length := by
  induction l with
  | nil =>
    simpa only [Pairing.edgeMonomial, List.map_nil, List.prod_nil, colorAverage_one,
      List.length_nil] using one_mem_lowDegree (tableCoordinate z) 0
  | cons e l ih =>
    by_cases hc : ∃ M : Pairing V, Pairing.ContainsList M (e::l)
    · obtain ⟨M₀, hm⟩ := hc
      have h₀ : Pairing.ContainsList M₀ l := fun f hf => hm f (List.mem_cons_of_mem _ hf)
      have hEdge : M₀.1 e.1 = e.2 := hm e (List.mem_cons_self)
      by_cases hv : e.1 ∈ Pairing.edgeSupport l ∨ e.2 ∈ Pairing.edgeSupport l
      · rw [Pairing.redundant_edgeMonomial hEdge h₀ hv]
        exact lowDegree_mono _ (by simp) ih
      · have he : e ∈ candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2) := by
          apply (mem_candidateEdges _ _ _ _).mpr
          refine ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h), ?_, rfl, rfl⟩
          intro heq
          exact M₀.partner_ne e.1 (hEdge.trans heq.symm)
        let D := ((candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)).card : ℝ)
        have hD : D ≠ 0 := by
          apply Nat.cast_ne_zero.mpr
          exact Finset.card_ne_zero.mpr ⟨e, he⟩
        have hr := colorAverage_recurrence z l e he M₀ h₀
        have hlin : tableCoordinate z (z e.1,z e.2) -
            (∑ v ∈ Pairing.edgeSupport l,
              if z v = z e.1 ∧ z (M₀.1 v) = z e.2 then (1:ℝ) else 0) • 1 ∈
            lowDegree (tableCoordinate z) 1 :=
          (lowDegree (tableCoordinate z) 1).sub_mem (coord_mem_lowDegree _ _)
            ((lowDegree (tableCoordinate z) 1).smul_mem _ (one_mem_lowDegree _ _))
        have hmem := mul_mem_lowDegree (tableCoordinate z) hlin ih
        rw [← hr] at hmem
        change D • colorAverage z (Pairing.edgeMonomial (e::l)) ∈
          lowDegree (tableCoordinate z) (1+l.length) at hmem
        have hh := (lowDegree (tableCoordinate z) (1+l.length)).smul_mem D⁻¹ hmem
        simpa only [smul_smul, inv_mul_cancel₀ hD, one_smul, Nat.add_comm,
          List.length_cons] using hh
    · rw [Pairing.edgeMonomial_zero_of_unsatisfiable _ hc, map_zero]
      exact Submodule.zero_mem _

lemma colorAverage_lowDegree (z : V → C) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    colorAverage z f ∈ lowDegree (tableCoordinate z) d := by
  apply Submodule.span_induction (p := fun f _ => colorAverage z f ∈
    lowDegree (tableCoordinate z) d) _ _ _ _ hf
  · rintro f ⟨l, hl, rfl⟩
    exact lowDegree_mono _ hl (colorAverage_monomial_mem z l)
  · simp
  · intro f g _ _ hf hg
    simpa only [map_add] using (lowDegree (tableCoordinate z) d).add_mem hf hg
  · intro c f _ hf
    simpa only [map_smul] using (lowDegree (tableCoordinate z) d).smul_mem c hf

end ColorPolynomials

section Substitution
variable {E : Type u_3} {I : Type u_4} {X : Type u_5} {Y : Type u_6}

lemma list_prod_mem_lowDegree (x : E → X → ℝ) (l : List I) (y : I → X → ℝ)
    (hy : ∀ i, y i ∈ lowDegree x 1) : (l.map y).prod ∈ lowDegree x l.length := by
  induction l with
  | nil => exact one_mem_lowDegree x 0
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm] using
      mul_mem_lowDegree x (hy i) ih

lemma lowDegree_substitute (x : E → X → ℝ) (y : I → X → ℝ)
    (hy : ∀ i, y i ∈ lowDegree x 1) (d : ℕ) : lowDegree y d ≤ lowDegree x d := by
  apply Submodule.span_le.mpr
  rintro f ⟨l, hl, rfl⟩
  exact lowDegree_mono x hl (list_prod_mem_lowDegree x l y hy)

end Substitution
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section TableCoordinates
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma tableCoordinate_symm (z : V → C) (a b : C) :
    tableCoordinate z (a,b) = tableCoordinate z (b,a) := by
  funext M
  unfold tableCoordinate
  rw [← Equiv.sum_comp M.1 (fun v => if z v = b ∧ z (M.1 v) = a then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro v _
  simp [M.partner_partner, and_comm]

lemma tableCoordinate_row_sum [Fintype C] (z : V → C) (a : C) :
    ∑ b, tableCoordinate z (a,b) = (histogram z a : ℝ) • 1 := by
  classical
  funext M
  simp only [Finset.sum_apply, tableCoordinate, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one]
  rw [Finset.sum_comm, histogram_cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases ha : z v = a
  · simp [ha]
  · simp [ha]

lemma tableCoordinate_diagonal [Fintype C] (z : V → C) (a : C) :
    tableCoordinate z (a,a) = (histogram z a : ℝ) • 1 -
      ∑ b ∈ Finset.univ.erase a, tableCoordinate z (a,b) := by
  classical
  rw [← tableCoordinate_row_sum]
  rw [eq_sub_iff_add_eq, add_comm]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ a)

end TableCoordinates

section ThreeCoordinates
variable {V : Type u_3} [Fintype V]

lemma tableCoordinate_offdiag_low (z : V → Fin 3) (a b : Fin 3) (hab : a ≠ b) :
    tableCoordinate z (a,b) ∈ lowDegree (crossCoordinate z) 1 := by
  have h01 : tableCoordinate z (0,1) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 0
  have h02 : tableCoordinate z (0,2) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 1
  have h12 : tableCoordinate z (1,2) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 2
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | exact h01 | exact h02 | exact h12 |
    rwa [tableCoordinate_symm]

lemma tableCoordinate_three_affine (z : V → Fin 3) (c : Fin 3 × Fin 3) :
    tableCoordinate z c ∈ lowDegree (crossCoordinate z) 1 := by
  classical
  obtain ⟨a,b⟩ := c
  by_cases hab : a = b
  · subst b
    rw [tableCoordinate_diagonal]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (one_mem_lowDegree _ _)
    · apply Submodule.sum_mem
      intro b hb
      simp only [Finset.mem_erase] at hb
      exact tableCoordinate_offdiag_low z a b hb.1.symm
  · exact tableCoordinate_offdiag_low z a b hab

lemma colorAverage_cross_lowDegree (z : V → Fin 3) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    colorAverage z f ∈ lowDegree (crossCoordinate z) d :=
  lowDegree_substitute (crossCoordinate z) (tableCoordinate z)
    (tableCoordinate_three_affine z) d (colorAverage_lowDegree z d f hf)

lemma colorAverage_polynomial (z : V → Fin 3) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    ∃ P ∈ lowDegree (fun i (v : Fin 3 → ℝ) => v i) d,
      ∀ M, colorAverage z f M = P (fun i => crossCoordinate z i M) :=
  lowDegree_lift _ _ _ (colorAverage_cross_lowDegree z d f hf)

end ThreeCoordinates

section TableRelation
variable {H : Type u_4} [Fintype H]

lemma tableCoordinate_relabel (z : H × Bool → Fin 3) (c : Fin 3 × Fin 3)
    (p : Equiv.Perm (H × Bool)) (M : Pairing (H × Bool)) :
    tableCoordinate z c (Pairing.relabel p M) = tableCoordinate (z ∘ p) c M := by
  classical
  unfold tableCoordinate
  apply Fintype.sum_equiv p.symm
  intro v
  split_ifs <;> simp_all [Function.comp_apply, Pairing.relabel_apply]

lemma three_order_indicator (a b x y : Fin 3) :
    (if x=a ∧ y=b then (1:ℝ) else 0) + (if y=a ∧ x=b then (1:ℝ) else 0) =
      (if a=b then 2 else 1) *
      (if threeEdgeType (x,y) = threeEdgeType (a,b) then (1:ℝ) else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [threeEdgeType, Fin.ext_iff]

lemma standard_tableCoordinate (z : H × Bool → Fin 3) (a b : Fin 3) :
    tableCoordinate z (a,b) standardPairing =
      (if a=b then (2:ℝ) else 1) * (threeTable z (threeEdgeType (a,b)) : ℝ) := by
  classical
  simp only [tableCoordinate, Fintype.sum_prod_type, Fintype.sum_bool,
    standardPairing, Equiv.prodCongr_apply]
  change (∑ i, ((if z (i,true)=a ∧ z (i,false)=b then (1:ℝ) else 0) +
    (if z (i,false)=a ∧ z (i,true)=b then (1:ℝ) else 0))) = _
  calc
    _ = ∑ i, (if a=b then (2:ℝ) else 1) *
        (if threeEdgeType (z (i,false),z (i,true)) = threeEdgeType (a,b) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [add_comm] using three_order_indicator a b (z (i,false)) (z (i,true))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact (histogram_cast_sum (threeEdgeType ∘ pairColorEquiv z) _).symm

lemma tableCoordinate_eq_table [DecidableEq H] (z : H × Bool → Fin 3)
    (M : Pairing (H × Bool)) (a b : Fin 3) :
    tableCoordinate z (a,b) M =
      (if a=b then (2:ℝ) else 1) * (M.table z (threeEdgeType (a,b)) : ℝ) := by
  classical
  obtain ⟨p, rfl⟩ := Pairing.exists_relabel (standardPairing (H := H)) M
  rw [tableCoordinate_relabel, Pairing.table_relabel, standardPairing_table,
    standard_tableCoordinate]

lemma crossCoordinate_eq_table [DecidableEq H] (z : H × Bool → Fin 3)
    (M : Pairing (H × Bool)) (i : Fin 3) :
    crossCoordinate z i M = (M.table z (threeEdgeType (crossPair i)) : ℝ) := by
  rw [crossCoordinate, tableCoordinate_eq_table]
  have hne : (crossPair i).1 ≠ (crossPair i).2 := by fin_cases i <;> decide
  rw [ite_eq_right hne, one_mul]

end TableRelation
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TablePolynomials ----
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section PredicateAverage
variable {X : Type u_1} [Fintype X]

lemma predicateAverage_apply (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = (∑ x, if P x then f x else 0) / Fintype.card {x // P x} := by
  simp only [predicateAverage, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

lemma predicateAverage_comp (P : X → Prop) (e : X ≃ X)
    (he : ∀ x, P (e x) ↔ P x) (f : X → ℝ) :
    predicateAverage P (f ∘ e) = predicateAverage P f := by
  rw [predicateAverage_apply, predicateAverage_apply]
  congr 1
  calc
    _ = ∑ x, if P (e x) then f (e x) else 0 := by simp only [he, Function.comp_apply]
    _ = _ := by
      apply Fintype.sum_equiv e
      intro x
      rfl

end PredicateAverage
end MatchingSmoothing

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ReynoldsAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

lemma predicateAverage_colorAverage (z : V → C) (P : Pairing V → Prop)
    (hP : ∀ (p : colorStabilizer z) M, P (Pairing.relabel p.1 M) ↔ P M)
    (f : Pairing V → ℝ) :
    predicateAverage P (colorAverage z f) = predicateAverage P f := by
  classical
  have hp (p : colorStabilizer z) :
      predicateAverage P (Pairing.act p.1 f) = predicateAverage P f := by
    exact predicateAverage_comp P (Pairing.relabelEquiv p.1⁻¹) (hP p⁻¹) f
  simp only [colorAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearEquiv.coe_coe, map_smul, map_sum]
  simp_rw [hp]
  simp [nsmul_eq_mul, Fintype.card_ne_zero]

end ReynoldsAverage

section TablePolynomial
variable {H : Type u_4} [Fintype H] [DecidableEq H]

lemma table_average_polynomial (z : H × Bool → Fin 3) (d : ℕ)
    (f : Pairing (H × Bool) → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    ∃ P ∈ lowDegree (fun i (v : Fin 3 → ℝ) => v i) d,
      ∀ t : Fin 6 → ℕ, (∃ M : Pairing (H × Bool), M.table z = t) →
        predicateAverage (fun M => M.table z = t) f =
          P (fun i => (t (threeEdgeType (crossPair i)) : ℝ)) := by
  obtain ⟨P, hP, hp⟩ := colorAverage_polynomial z d f hf
  refine ⟨P, hP, ?_⟩
  intro t ht
  have hInv (p : colorStabilizer z) (M : Pairing (H × Bool)) :
      (Pairing.relabel p.1 M).table z = t ↔ M.table z = t := by
    rw [Pairing.table_relabel]
    have hz : z ∘ p.1 = z := funext p.property
    rw [hz]
  rw [← predicateAverage_colorAverage z _ hInv]
  apply predicateAverage_of_constant _ _ ht
  intro M hM
  rw [hp]
  congr 1
  funext i
  rw [crossCoordinate_eq_table, hM]

end TablePolynomial
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.table_average_polynomial := @_root_.OAI.MatchingSmoothing.table_average_polynomial
