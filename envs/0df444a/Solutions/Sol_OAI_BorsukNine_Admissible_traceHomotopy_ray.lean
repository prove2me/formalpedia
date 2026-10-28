-- Prove2me | solution 1 for OAI.BorsukNine.Admissible.traceHomotopy_ray
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:05:19.3409+00:00
-- url     : https://prove2.me/submissions/20c70118-ca02-4198-9cbc-cc09e02b5b8c

import Mathlib
import Definitions.Def_OAIQ058B000

section
-- module Solutions.OAIQ058_BK.Compat
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_ReflectionTransport
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ReflectionTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma householder_send {c x : E} (h : ‖c‖ = ‖x‖) : householder c x c = x := by
  have hh := Submodule.reflection_sub (v := c) (w := -x) (by simpa using h)
  rw [sub_neg_eq_add,Submodule.reflection_orthogonal_apply] at hh
  exact neg_injective hh

end ReflectionTransport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SignedExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SignedExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

omit [Nonempty ν] [Fintype ι] in
lemma signedExtension_odd (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    signedExtension f (-A) = -signedExtension f A := by
  simp [signedExtension, CFC.posPart_neg, CFC.negPart_neg]

end SignedExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SymmetricCoordinates
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SymmetricCoordinates
variable {ν : Type*} [Fintype ν] [LinearOrder ν]

omit [Fintype ν] in
lemma symmetricCoordinates_upper (x : EuclideanSpace ℝ (UpperTriangle ν))
    (i j : ν) (hij : i ≤ j) : symmetricCoordinates x i j = x ⟨(i,j), hij⟩ := by
  change (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) = _
  exact dite_eq_left hij

omit [Fintype ν] in
lemma symmetricCoordinates_selfAdjoint (x : EuclideanSpace ℝ (UpperTriangle ν)) :
    IsSelfAdjoint (symmetricCoordinates x) := by
  change (symmetricCoordinates x)ᴴ = symmetricCoordinates x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change (if h : j ≤ i then x ⟨(j,i),h⟩ else x ⟨(i,j),le_of_not_ge h⟩) =
    (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have he := le_antisymm hij hji
      subst j
      rfl
    · simp [hij, hji]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [hij, hji]

omit [Fintype ν] in
lemma symmetricCoordinates_injective : Function.Injective (symmetricCoordinates (ν := ν)) := by
  intro x y hxy
  apply PiLp.ext
  intro p
  have h := congrArg (fun A : Matrix ν ν ℝ => A p.val.1 p.val.2) hxy
  simpa only [symmetricCoordinates_upper _ _ _ p.property] using h

end SymmetricCoordinates

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Equivariance
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]

section Cone

lemma cone_simplex (K : PreAbstractSimplicialComplex V) (a : V) {s : Finset V} (hs : s ∈ K) :
    cone K a (simplex K s) = if a ∈ s then 0 else simplex K (insert a s) := by
  simp [simplex_of_mem K hs, cone, Finsupp.linearCombination_single]

lemma cone_boundary_simplex (K : PreAbstractSimplicialComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) (ha : a ∉ s) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases hc : s.card = 1
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
    have hab : a ≠ b := by simpa using ha
    have hs' : ({a} : Finset V) ∈ K :=
      (K.isRelLowerSet_faces hinsert).2 (by simp) (Finset.singleton_nonempty a)
    rw [cone_simplex K a hs, ite_eq_right ha, boundary_simplex K hinsert,
      boundary_simplex K hs, augmentation_simplex K hs]
    simp [ha, Finset.erase_insert_of_ne hab]
  · have hn : s.Nonempty := (K.isRelLowerSet_faces hs).1
    have hc' : 2 ≤ s.card := by have := hn.card_pos; omega
    have he (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
      omega
    have heK (b : V) (hb : b ∈ s) : s.erase b ∈ K :=
      (K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (he b hb)
    rw [cone_simplex K a hs, ite_eq_right ha, boundary_simplex K hinsert,
      augmentation_simplex K hs, ite_eq_right hc, zero_smul, add_zero,
      boundary_simplex K hs, map_sum, Finset.sum_insert ha, Finset.erase_insert ha]
    apply congrArg (fun z => simplex K s + z)
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := by intro hh; subst b; exact ha hb
    have hn : a ∉ s.erase b := fun hh => ha (Finset.mem_of_mem_erase hh)
    rw [cone_simplex K a (heK b hb), ite_eq_right hn, Finset.erase_insert_of_ne hab]

lemma cone_boundary_simplex_all (K : PreAbstractSimplicialComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases ha : a ∈ s
  · by_cases hc : s.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
      have hab : a = b := Finset.mem_singleton.mp ha
      subst b
      rw [cone_simplex K a hs, ite_eq_left ha, map_zero, boundary_simplex K hs,
        augmentation_simplex K hs]
      simp [chain_add_self]
    · have hcn (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
        have hn := (K.isRelLowerSet_faces hs).1.card_pos
        rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
        omega
      have hcon : cone K a (boundary K (simplex K s)) = simplex K s := by
        rw [boundary_simplex K hs, map_sum]
        rw [Finset.sum_eq_single a]
        · rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) (hcn a ha))]
          simp [Finset.insert_erase ha]
        · intro b hb hba
          rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (hcn b hb))]
          simp [Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩]
        · exact fun hn => False.elim (hn ha)
      rw [cone_simplex K a hs, ite_eq_left ha, map_zero, hcon,
        augmentation_simplex K hs, ite_eq_right hc, zero_smul, add_zero, chain_add_self]
  · exact cone_boundary_simplex K a hs hinsert ha

omit [DecidableEq V] in
lemma chain_eq_sum (K : PreAbstractSimplicialComplex V) (c : Chain K) :
    c = ∑ s ∈ c.support, c s • simplex K s.val := by
  conv_lhs => rw [← c.sum_single]
  simp [Finsupp.sum, simplex_of_mem K, Finsupp.smul_single]

lemma cone_boundary (K : PreAbstractSimplicialComplex V) (a : V) (c : Chain K)
    (hc : ∀ s ∈ c.support, insert a s.val ∈ K) :
    boundary K (cone K a c) = c + cone K a (boundary K c) +
      augmentation K c • simplex K {a} := by
  classical
  conv_lhs => rw [chain_eq_sum K c]
  rw [map_sum, map_sum]
  have he (s : { s : Finset V // s ∈ K }) (hs : s ∈ c.support) :
      boundary K (cone K a (c s • simplex K s.val)) =
        c s • simplex K s.val + cone K a (boundary K (c s • simplex K s.val)) +
        augmentation K (c s • simplex K s.val) • simplex K {a} := by
    rw [map_smul, map_smul, cone_boundary_simplex_all K a s.property (hc s hs)]
    simp only [smul_add, map_smul, smul_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← map_sum, ← map_sum, ← Finset.sum_smul, ← map_sum, ← chain_eq_sum K c]

end Cone

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SmithTheory_Involution
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
section Involution
variable {ι : Type*}

lemma involutionNorm_sq (τ : ι ≃ ι) (hτ : Function.Involutive τ) :
    (involutionNorm τ).comp (involutionNorm τ) = 0 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro a
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  simp only [LinearMap.comp_apply, involutionNorm_apply, hsymm, ht,
    LinearMap.zero_apply, Finsupp.zero_apply]
  simp [add_comm, CharTwo.add_self_eq_zero]

end Involution

end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_NormMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma simplex_mem_degree (K : PreAbstractSimplicialComplex V) {s : Finset V}
    (hs : s ∈ K) : simplex K s ∈ degreeChains K s.card := by
  rw [simplex_of_mem K hs]
  exact Finsupp.single_mem_supported _ _ rfl

omit [DecidableEq V] [DecidableEq W] in
lemma grade_map (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (d e : ℕ)
    (hT : ∀ s ∈ K, s.card = d → T (simplex K s) ∈ degreeChains L e) :
    degreeChains K d ≤ (degreeChains L e).comap T := by
  rw [degreeChains, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, rfl⟩
  change T (Finsupp.single s 1) ∈ degreeChains L e
  rw [← simplex_of_mem K s.property]
  exact hT s.val s.property hs

omit [DecidableEq V] in
lemma mapChains_degree (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (f : V → W) (hf : ∀ s ∈ K, s.image f ∈ L) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree L (hf s hs)
  · exact Submodule.zero_mem _

omit [DecidableEq V] in
lemma degreeChains_eq_bot_of_card_bound (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hK : ∀ s ∈ K, s.card < d) : degreeChains K d = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  apply Finsupp.ext
  intro s
  have hne : s.val.card ≠ d := ne_of_lt (hK s.val s.property)
  exact (Finsupp.mem_supported' F₂ c).mp hc s hne

omit [DecidableEq V] in
lemma augmentation_eq_zero_of_degree (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hd : d ≠ 1) {c : Chain K} (hc : c ∈ degreeChains K d) : augmentation K c = 0 := by
  have hle : degreeChains K d ≤ LinearMap.ker (augmentation K) := by
    rw [degreeChains, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    change augmentation K (Finsupp.single s 1) = 0
    rw [← simplex_of_mem K s.property, augmentation_simplex K s.property]
    simp [show s.val.card ≠ 1 by simpa only [Set.mem_ofPred_eq] using hs ▸ hd]
  exact hle hc

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MemSupportSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma mem_support_simplex (K : PreAbstractSimplicialComplex V) (s : Finset V)
    (t : {s : Finset V // s ∈ K}) :
    t ∈ (simplex K s).support ↔ t.val = s := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs, Finsupp.support_single _ one_ne_zero]
    simp only [Finset.mem_singleton, Subtype.ext_iff]
  · simp only [simplex, dite_eq_right hs, Finsupp.support_zero, Finset.notMem_empty, false_iff]
    intro he
    exact hs (he ▸ t.property)

omit [DecidableEq V] [DecidableEq W] in
lemma support_linearMap (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (c : Chain K)
    {t : {s : Finset W // s ∈ L}} (ht : t ∈ (T c).support) :
    ∃ s ∈ c.support, t ∈ (T (simplex K s.val)).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (T c) t = 0 := by
    conv_lhs => rw [chain_eq_sum K c]
    rw [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    rw [map_smul, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp (hn s hs), smul_zero]
  exact (Finsupp.mem_support_iff.mp ht) hh

lemma support_cone (K : PreAbstractSimplicialComplex V) (a : V) (c : Chain K)
    {t : {s : Finset V // s ∈ K}} (ht : t ∈ (cone K a c).support) :
    ∃ s ∈ c.support, a ∉ s.val ∧ t.val = insert a s.val := by
  obtain ⟨s, hs, ht⟩ := support_linearMap K K (cone K a) c ht
  rw [cone_simplex K a s.property] at ht
  split_ifs at ht with ha
  · simp at ht
  · exact ⟨s, hs, ha, (mem_support_simplex K _ t).mp ht⟩

lemma cone_degree (K : PreAbstractSimplicialComplex V) (a : V) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K (d+1)).comap (cone K a) := by
  intro c hc t ht
  obtain ⟨s, hs, ha, he⟩ := support_cone K a c ht
  change t.val.card = d+1
  rw [he, Finset.card_insert_of_notMem ha, hc hs]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SubdivSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma subdivSimplex_one (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    {s : Finset V} (hc : s.card = 1) : subdivSimplex L b s = simplex L {b s} := by
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  rw [subdivSimplex, dite_eq_left hn, ite_eq_left hc]

lemma subdivSimplex_many (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    {s : Finset V} (hn : s.Nonempty) (hc : s.card ≠ 1) :
    subdivSimplex L b s = cone L (b s) (∑ a ∈ s, subdivSimplex L b (s.erase a)) := by
  rw [subdivSimplex, dite_eq_left hn, ite_eq_right hc]
  exact congrArg (cone L (b s)) (Finset.sum_attach s (fun a : V => subdivSimplex L b (s.erase a)))

omit [DecidableEq V] [DecidableEq W] in
lemma vertexCarrier_mono (b : Finset V → W) {s t : Finset V} (hst : s ⊆ t) :
    vertexCarrier b s ⊆ vertexCarrier b t := by
  rintro w ⟨u, hu, hus, hb⟩
  exact ⟨u, hu, hus.trans hst, hb⟩

omit [DecidableEq V] [DecidableEq W] in
lemma center_mem_carrier (b : Finset V → W) {s : Finset V} (hs : s.Nonempty) :
    b s ∈ vertexCarrier b s := ⟨s, hs, Finset.Subset.refl _, rfl⟩

lemma support_sum_chains (L : PreAbstractSimplicialComplex W) {α : Type*}
    (s : Finset α) (c : α → Chain L) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (∑ a ∈ s, c a).support) : ∃ a ∈ s, t ∈ (c a).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (∑ a ∈ s, c a) t = 0 := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero (fun a ha => Finsupp.notMem_support_iff.mp (hn a ha))
  exact Finsupp.mem_support_iff.mp ht hh

lemma subdivSimplex_carrier (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (subdivSimplex L b s).support) : ↑t.val ⊆ vertexCarrier b s := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, mem_support_simplex] at ht
      rw [ht]
      exact Finset.singleton_subset_set_iff.mpr (center_mem_carrier b hn)
    · rw [subdivSimplex_many L b hn hc] at ht
      obtain ⟨u, hu, _, htu⟩ := support_cone L (b s) _ ht
      obtain ⟨a, ha, hua⟩ := support_sum_chains L s _ hu
      have hu' := ih (s.erase a) (Finset.erase_ssubset ha) hua
      rw [htu, Finset.coe_insert]
      exact Set.insert_subset (center_mem_carrier b hn)
        (hu'.trans (vertexCarrier_mono b (Finset.erase_subset a s)))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SimplexMemDegreeAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma simplex_mem_degree_all (K : PreAbstractSimplicialComplex V) (s : Finset V) :
    simplex K s ∈ degreeChains K s.card := by
  classical
  by_cases hs : s ∈ K
  · exact simplex_mem_degree K hs
  · simp only [simplex, dite_eq_right hs]
    exact Submodule.zero_mem _

lemma subdivSimplex_degree (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) : subdivSimplex L b s ∈ degreeChains L s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · rw [subdivSimplex_empty]
      exact Submodule.zero_mem _
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, hc]
      exact simplex_mem_degree_all L {b s}
    · rw [subdivSimplex_many L b hn hc]
      have hsum : (∑ a ∈ s, subdivSimplex L b (s.erase a)) ∈ degreeChains L (s.card-1) := by
        apply Submodule.sum_mem
        intro a ha
        have hh := ih (s.erase a) (Finset.erase_ssubset ha)
        simpa only [Finset.card_erase_of_mem ha] using hh
      have hpos := hn.card_pos
      simpa only [Submodule.mem_comap, Nat.sub_add_cancel hpos] using
        cone_degree L (b s) (s.card-1) hsum

omit [DecidableEq V] [DecidableEq W] in
lemma SubdivisionCarrier.center (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) : {b s} ∈ L :=
  hb s hs {b s} (Finset.singleton_nonempty _) (Finset.singleton_subset_set_iff.mpr
    (center_mem_carrier b (K.isRelLowerSet_faces hs).1))

lemma subdivSimplex_augmentation (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    augmentation L (subdivSimplex L b s) = augmentation K (simplex K s) := by
  rw [augmentation_simplex K hs]
  by_cases hc : s.card = 1
  · rw [subdivSimplex_one L b hc, augmentation_simplex L (hb.center K L b hs)]
    simp [hc]
  · rw [ite_eq_right hc]
    exact augmentation_eq_zero_of_degree L _ hc (subdivSimplex_degree L b s)

lemma subdivMap_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  simp [simplex_of_mem K hs, subdivMap, Finsupp.linearCombination_single]

lemma subdivMap_simplex_subset (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) : subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact subdivMap_simplex K L b ((K.isRelLowerSet_faces ht).2 hs hn)

lemma subdivMap_augmentation (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (augmentation L).comp (subdivMap K L b) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_augmentation K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]

lemma subdivMap_boundary_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (boundary K (simplex K s)) =
      ∑ a ∈ s, subdivSimplex L b (s.erase a) := by
  rw [boundary_simplex K hs, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact subdivMap_simplex_subset K L b hs (Finset.erase_subset a s)

lemma subdivSimplex_boundary (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    boundary L (subdivSimplex L b s) = subdivMap K L b (boundary K (simplex K s)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn := (K.isRelLowerSet_faces hs).1
    by_cases hc : s.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      rw [subdivSimplex_one L b hc, boundary_simplex L (hb.center K L b hs),
        boundary_simplex K hs]
      simp
    · have hd : boundary L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have he : boundary L (subdivMap K L b (boundary K (simplex K s))) =
            subdivMap K L b (boundary K (boundary K (simplex K s))) := by
          rw [boundary_simplex K hs]
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rcases (s.erase a).eq_empty_or_nonempty with heq | hne
          · simp [heq]
          · have hK : s.erase a ∈ K := (K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) hne
            rw [subdivMap_simplex K L b hK]
            exact ih (s.erase a) (Finset.erase_ssubset ha) hK
        rw [he, boundary_twice_simplex K hs, map_zero]
      have hε : augmentation L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have hh := LinearMap.congr_fun (subdivMap_augmentation K L b hb)
          (boundary K (simplex K s))
        rw [LinearMap.comp_apply, augmentation_boundary_simplex K hs] at hh
        exact hh
      have hcone : ∀ t ∈ (subdivMap K L b (boundary K (simplex K s))).support,
          insert (b s) t.val ∈ L := by
        rw [subdivMap_boundary_simplex K L b hs]
        intro t ht
        obtain ⟨a, ha, hta⟩ := support_sum_chains L s _ ht
        have ht' := (subdivSimplex_carrier L b _ hta).trans
          (vertexCarrier_mono b (Finset.erase_subset a s))
        apply hb s hs _ (Finset.insert_nonempty _ _)
        rw [Finset.coe_insert]
        exact Set.insert_subset (center_mem_carrier b hn) ht'
      rw [subdivSimplex_many L b hn hc, ← subdivMap_boundary_simplex K L b hs,
        cone_boundary L (b s) _ hcone, hd, hε, map_zero, zero_smul, add_zero, add_zero]

lemma subdivMap_boundary (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (boundary L).comp (subdivMap K L b) = (subdivMap K L b).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_boundary K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SignedVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma cross_card (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) : s.card ≤ n := by
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hs.2.2).symm
    _ ≤ (Finset.range n).card := Finset.card_le_card (by
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv))
    _ = n := Finset.card_range n

lemma cross_singleton (n i : ℕ) (hi : i < n) (b : Bool) :
    ({(i,b)} : Finset SignedVertex) ∈ cross n := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · simpa using hi
  · simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (i,b)

lemma cross_insert (n i : ℕ) (hi : i < n) (s : Finset SignedVertex)
    (hs : s ∈ cross n) (hsi : ∀ v ∈ s, v.1 < i) (b : Bool) :
    insert (i,b) s ∈ cross n := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hi
    · exact hs.2.1 v hv
  · intro v hv w hw he
    rcases Finset.mem_insert.mp hv with rfl | hv <;>
      rcases Finset.mem_insert.mp hw with rfl | hw
    · rfl
    · exact False.elim ((ne_of_lt (hsi w hw)) he.symm)
    · exact False.elim ((ne_of_lt (hsi v hv)) he)
    · exact hs.2.2 hv hw he

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma support_mapChains_injective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (hf : Function.Injective f)
    (c : Chain K) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (mapChains K L f c).support) :
    ∃ s ∈ c.support, t.val = s.val.image f := by
  obtain ⟨s, hs, hst⟩ := support_linearMap K L (mapChains K L f) c ht
  rw [mapChains_simplex K L f s.property, mapSimplex,
    ite_eq_left (Finset.card_image_iff.mpr hf.injOn), mem_support_simplex] at hst
  exact ⟨s, hs, hst⟩

lemma normMap_sq (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e) :
    (normMap K e).comp (normMap K e) = 0 := by
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_sq _ (faceEquiv_involutive K e he hi)

lemma normMap_degree (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K d).comap (normMap K e) := by
  intro c hc
  exact (degreeChains K d).add_mem hc (mapChains_degree K K e he d hc)

lemma crossTower_support (n i : ℕ) {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (crossTower n i).support) : ∀ v ∈ s.val, v.1 ≤ i := by
  induction i generalizing s with
  | zero =>
    have he := (mem_support_simplex (cross n) {(0,false)} s).mp hs
    rw [he]
    intro v hv
    have he' := Finset.mem_singleton.mp hv
    exact he' ▸ Nat.le_refl 0
  | succ i ih =>
    obtain ⟨t, ht, _, he⟩ := support_cone (cross n) (i+1,false) _ hs
    rw [he]
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact le_rfl
    · have hu : t ∈ (crossTower n i).support ∪
          (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
        Finsupp.support_add ht
      rcases Finset.mem_union.mp hu with ht | ht
      · exact (ih ht v hv).trans (Nat.le_succ i)
      · obtain ⟨u, hu, he⟩ := support_mapChains_injective (cross n) (cross n) flip
          flip.injective _ ht
        rw [he] at hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact (ih hu w hw).trans (Nat.le_succ i)

lemma crossTower_degree (n i : ℕ) : crossTower n i ∈ degreeChains (cross n) (i+1) := by
  induction i with
  | zero => exact simplex_mem_degree_all (cross n) {(0,false)}
  | succ i ih =>
    exact cone_degree (cross n) (i+1,false) (i+1)
      (normMap_degree (cross n) flip (cross_flip_forward n) (i+1) ih)

lemma crossTower_cone_faces (n i : ℕ) (hi : i+1 < n)
    {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (normMap (cross n) flip (crossTower n i)).support) :
    insert (i+1,false) s.val ∈ cross n := by
  apply cross_insert n (i+1) hi s.val s.property
  intro v hv
  have hu : s ∈ (crossTower n i).support ∪
      (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
    Finsupp.support_add hs
  rcases Finset.mem_union.mp hu with hs | hs
  · exact Nat.lt_succ_of_le (crossTower_support n i hs v hv)
  · obtain ⟨t, ht, he⟩ := support_mapChains_injective (cross n) (cross n) flip
      flip.injective _ hs
    rw [he] at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.lt_succ_of_le (crossTower_support n i ht w hw)

lemma crossTower_norm_boundary (n i : ℕ) (hi : i < n) :
    boundary (cross n) (normMap (cross n) flip (crossTower n i)) = 0 := by
  induction i with
  | zero =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n 0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n) (simplex (cross n) {(0,false)})) = 0
    rw [boundary_simplex (cross n) (cross_singleton n 0 hi false)]
    simp
  | succ i ih =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n (i+1))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n)
      (cone (cross n) (i+1,false) (normMap (cross n) flip (crossTower n i)))) = 0
    rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
      ih (by omega)]
    have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n i)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
    rw [ha, map_zero, zero_smul, add_zero, add_zero]
    exact LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _

lemma crossTower_boundary (n i : ℕ) (hi : i+1 < n) :
    boundary (cross n) (crossTower n (i+1)) = normMap (cross n) flip (crossTower n i) := by
  change boundary (cross n) (cone (cross n) (i+1,false)
    (normMap (cross n) flip (crossTower n i))) = _
  rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
    crossTower_norm_boundary n i (by omega)]
  have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
    (crossTower n i)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
  rw [ha, map_zero, zero_smul, add_zero, add_zero]

lemma crossTower_augmentation (n : ℕ) (hn : 0 < n) :
    augmentation (cross n) (crossTower n 0) = 1 := by
  rw [crossTower, augmentation_simplex (cross n) (cross_singleton n 0 hn false)]
  simp

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SmithTheory_CharacteristicCochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SmithTheory

section CharacteristicCochains
variable {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
variable (d N : P →ₗ[ZMod 2] P)

lemma smithDegree_norm (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) (c : P) :
    smithDegree d N hd hcomm hexact φ n (N c) =
      (smithCochain d N hd hcomm hexact φ n).val c :=
  LinearMap.congr_fun (smithLift_comp_norm d N hexact _) c

lemma smithCochain_succ (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) (c : P) :
    (smithCochain d N hd hcomm hexact φ (n+1)).val c =
      smithDegree d N hd hcomm hexact φ n (d c) := rfl

variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]

lemma smithDegree_natural
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N)
    (d' N' : Q →ₗ[ZMod 2] Q) (hd' : d'.comp d' = 0) (hcomm' : d'.comp N' = N'.comp d')
    (hexact' : LinearMap.ker N' ≤ LinearMap.range N') (φ' : SmithCocycle d' N')
    (T : P →ₗ[ZMod 2] Q) (hTd : d'.comp T = T.comp d) (hTN : N'.comp T = T.comp N)
    (hTφ : φ'.val.comp T = φ.val) (n : ℕ) (c : P) (hNc : N c = 0) (hdc : d c = 0) :
    smithDegree d' N' hd' hcomm' hexact' φ' n (T c) =
      smithDegree d N hd hcomm hexact φ n c := by
  induction n generalizing c with
  | zero =>
    obtain ⟨x,hx⟩ := hexact hNc
    rw [← hx, ← LinearMap.comp_apply T N, ← hTN, LinearMap.comp_apply,
      smithDegree_norm, smithDegree_norm]
    exact LinearMap.congr_fun hTφ x
  | succ n ih =>
    obtain ⟨x,hx⟩ := hexact hNc
    rw [← hx, ← LinearMap.comp_apply T N, ← hTN, LinearMap.comp_apply,
      smithDegree_norm, smithDegree_norm, smithCochain_succ, smithCochain_succ,
      ← LinearMap.comp_apply d' T, hTd, LinearMap.comp_apply]
    apply ih
    · rw [← LinearMap.comp_apply N d, ← hcomm, LinearMap.comp_apply, hx, hdc]
    · exact LinearMap.congr_fun hd x

end CharacteristicCochains
end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CharacteristicDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset BorsukNine.SmithTheory

section NaturalDegree
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma characteristicDegree_natural
    (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (L : PreAbstractSimplicialComplex W) (d : W ≃ W)
    (hd : ∀ s, s ∈ L ↔ s.image d ∈ L) (hdi : Function.Involutive d)
    (hdfree : ∀ s ∈ L, s.image d ≠ s)
    (T : Chain K →ₗ[F₂] Chain L)
    (hTbd : (boundary L).comp T = T.comp (boundary K))
    (hTN : (normMap L d).comp T = T.comp (normMap K e))
    (hTa : (augmentation L).comp T = augmentation K)
    (n : ℕ) (c : Chain K) (hcN : normMap K e c = 0) (hcb : boundary K c = 0) :
    characteristicDegree L d hd hdi hdfree n (T c) =
      characteristicDegree K e he hi hfree n c := by
  exact smithDegree_natural (boundary K) (normMap K e) (boundary_sq K)
    (boundary_normMap K e (fun s hs => (he s).mp hs)) (normMap_exact K e he hi hfree)
    (characteristicAugmentation K e he) (boundary L) (normMap L d) (boundary_sq L)
    (boundary_normMap L d (fun s hs => (hd s).mp hs)) (normMap_exact L d hd hdi hdfree)
    (characteristicAugmentation L d hd) T hTbd hTN hTa n c hcN hcb

end NaturalDegree

lemma crossFundamental_norm (n : ℕ) : normMap (cross n) flip (crossFundamental n) = 0 :=
  LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _

lemma crossFundamental_boundary (n : ℕ) (hn : 0 < n) :
    boundary (cross n) (crossFundamental n) = 0 :=
  crossTower_norm_boundary n (n-1) (by omega)

lemma crossFundamental_degree (n : ℕ) (hn : 0 < n) :
    crossFundamental n ∈ degreeChains (cross n) n := by
  have h := normMap_degree (cross n) flip (cross_flip_forward n) (n-1+1)
    (crossTower_degree n (n-1))
  change normMap (cross n) flip (crossTower n (n-1)) ∈
    degreeChains (cross n) (n-1+1) at h
  simpa only [crossFundamental, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h

lemma characteristicCochain_crossTower (n i : ℕ) (hi : i < n) :
    (smithCochain (boundary (cross n)) (normMap (cross n) flip) (boundary_sq (cross n))
      (boundary_normMap (cross n) flip (cross_flip_forward n))
      (normMap_exact (cross n) flip (cross_flip n) flip_involutive (cross_free n))
      (characteristicAugmentation (cross n) flip (cross_flip n)) i).val
        (crossTower n i) = 1 := by
  induction i with
  | zero => exact crossTower_augmentation n (by omega)
  | succ i ih =>
    rw [smithCochain_succ, crossTower_boundary n i hi, smithDegree_norm]
    exact ih (by omega)

lemma characteristicDegree_crossFundamental (n : ℕ) (hn : 0 < n) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) (crossFundamental n) = 1 := by
  unfold characteristicDegree crossFundamental
  rw [smithDegree_norm]
  exact characteristicCochain_crossTower n (n-1) (by omega)

lemma cross_equivariant_degree_one (n : ℕ) (hn : 0 < n)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross n))
    (hTbd : (boundary (cross n)).comp T = T.comp (boundary (cross n)))
    (hTN : (normMap (cross n) flip).comp T = T.comp (normMap (cross n) flip))
    (hTa : (augmentation (cross n)).comp T = augmentation (cross n)) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) (T (crossFundamental n)) = 1 := by
  rw [characteristicDegree_natural (cross n) flip (cross_flip n) flip_involutive
    (cross_free n) (cross n) flip (cross_flip n) flip_involutive (cross_free n)
    T hTbd hTN hTa (n-1) (crossFundamental n) (crossFundamental_norm n)
    (crossFundamental_boundary n hn), characteristicDegree_crossFundamental n hn]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

section Coefficients
variable {V : Type*} [DecidableEq V] (K : PreAbstractSimplicialComplex V)

omit [DecidableEq V] in
lemma degreeChains_card_of_ne_zero (n : ℕ) {c : Chain K}
    (hc : c ∈ degreeChains K n) (s : {s : Finset V // s ∈ K}) (hs : c s ≠ 0) :
    s.val.card = n := by
  by_contra h
  exact hs ((Finsupp.mem_supported' F₂ c).mp hc s h)

lemma simplex_coeff (s : Finset V) (t : {t : Finset V // t ∈ K}) :
    simplex K s t = if s = t.val then 1 else 0 := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs]
    simp only [Finsupp.single_apply]
    congr 1
    exact propext Subtype.ext_iff
  · have hst : s ≠ t.val := fun h => hs (h ▸ t.property)
    simp [simplex, hs, hst]

lemma boundary_simplex_coeff {s : Finset V} (hs : s ∈ K)
    (t : {t : Finset V // t ∈ K}) (hcard : t.val.card + 1 = s.card) :
    boundary K (simplex K s) t = if t.val ⊆ s then 1 else 0 := by
  classical
  rw [boundary_simplex K hs, Finsupp.finsetSum_apply]
  simp_rw [simplex_coeff]
  by_cases hts : t.val ⊆ s
  · rw [ite_eq_left hts]
    obtain ⟨a,ha,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts,hcard⟩
    rw [Finset.sum_insert ha, Finset.erase_insert ha, ite_eq_left rfl]
    have hz : ∀ b ∈ t.val, (if (insert a t.val).erase b = t.val then (1:F₂) else 0) = 0 := by
      intro b hb
      rw [ite_eq_right]
      intro he
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      have hh : a ∈ (insert a t.val).erase b := Finset.mem_erase.mpr
        ⟨hab, Finset.mem_insert_self _ _⟩
      exact ha (he ▸ hh)
    rw [Finset.sum_eq_zero hz, add_zero]
  · rw [ite_eq_right hts]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ite_eq_right]
    intro he
    exact hts (he ▸ Finset.erase_subset a s)

end Coefficients

lemma cross_top_exists_signs (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n)
    (hcard : s.card = n) : ∃ b : Fin n → Bool, s = crossFacet n b := by
  classical
  have hproj : s.image Prod.fst = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv)
    · rw [Finset.card_image_iff.mpr hs.2.2, Finset.card_range, hcard]
  have hex (i : Fin n) : ∃ v ∈ s, v.1 = i.val := by
    apply Finset.mem_image.mp
    rw [hproj]
    exact Finset.mem_range.mpr i.isLt
  choose v hv hvi using hex
  refine ⟨fun i => (v i).2, ?_⟩
  ext w
  constructor
  · intro hw
    let i : Fin n := ⟨w.1,hs.2.1 w hw⟩
    have he : w = v i := hs.2.2 hw (hv i) (hvi i).symm
    apply (mem_crossFacet n _ w).mpr
    refine ⟨i, ?_⟩
    apply Prod.ext
    · rfl
    · change w.2 = (v i).2
      exact congrArg Prod.snd he
  · intro hw
    obtain ⟨i,rfl⟩ := (mem_crossFacet n _ w).mp hw
    have he : (i.val,(v i).2) = v i := Prod.ext (hvi i).symm rfl
    rw [he]
    exact hv i

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MapChainsEquivSimplexAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W U : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq U]

omit [DecidableEq W] [DecidableEq U] in
lemma mapChains_equiv_simplex_all (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (s : Finset V) :
    mapChains K K e (simplex K s) = simplex K (s.image e) := by
  classical
  by_cases hs : s ∈ K
  · rw [mapChains_simplex K K e hs, mapSimplex,
      ite_eq_left (Finset.card_image_iff.mpr e.injective.injOn)]
  · have ht : s.image e ∉ K := (he s).not.mp hs
    simp [simplex, hs, ht]

omit [DecidableEq W] [DecidableEq U] in
lemma cone_equivariant (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (a : V) :
    (mapChains K K e).comp (cone K a) = (cone K (e a)).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hm := mapChains_equiv_simplex_all K e he s.val
  have hc := cone_simplex K a s.property
  have hsc := cone_simplex K (e a) ((he s.val).mp s.property)
  have hh : mapChains K K e (cone K a (simplex K s.val)) =
      cone K (e a) (mapChains K K e (simplex K s.val)) := by
    rw [hc, hm, hsc]
    by_cases ha : a ∈ s.val
    · rw [ite_eq_left ha, ite_eq_left (Finset.mem_image_of_mem e ha), map_zero]
    · have hna : e a ∉ s.val.image e := by
        intro h
        obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h
        exact ha (e.injective heq ▸ hb)
      rw [ite_eq_right ha, ite_eq_right hna, mapChains_equiv_simplex_all K e he,
        Finset.image_insert]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

omit [DecidableEq U] in
lemma subdivSimplex_equivariant (L : PreAbstractSimplicialComplex W)
    (e : V ≃ V) (d : W ≃ W) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) (s : Finset V) :
    mapChains L L d (subdivSimplex L b s) = subdivSimplex L b (s.image e) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp
    have hc : (s.image e).card = s.card := Finset.card_image_iff.mpr e.injective.injOn
    by_cases hs : s.card = 1
    · rw [subdivSimplex_one L b hs, subdivSimplex_one L b (hc.trans hs),
        mapChains_equiv_simplex_all L d hd, Finset.image_singleton, hb]
    · rw [subdivSimplex_many L b hn hs,
        subdivSimplex_many L b (hn.image e) (by omega)]
      have hcone := LinearMap.congr_fun (cone_equivariant L d hd (b s))
        (∑ a ∈ s, subdivSimplex L b (s.erase a))
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcone
      rw [hcone, map_sum, hb, Finset.sum_image (fun a _ b _ he => e.injective he)]
      apply congrArg (cone L (d (b s)))
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih (s.erase a) (Finset.erase_ssubset ha), image_erase_of_injOn e s e.injective.injOn ha]

omit [DecidableEq U] in
lemma subdivMap_equivariant (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (mapChains L L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hh : mapChains L L d (subdivMap K L b (simplex K s.val)) =
      subdivMap K L b (mapChains K K e (simplex K s.val)) := by
    rw [subdivMap_simplex K L b s.property, subdivSimplex_equivariant L e d hd b hb,
      mapChains_equiv_simplex_all K e he, subdivMap_simplex K L b ((he s.val).mp s.property)]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

omit [DecidableEq U] in
lemma subdivMap_norm (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (normMap L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, subdivMap_equivariant K L e d he hd b hb]

omit [DecidableEq U] in
lemma subdivMap_degree (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (subdivMap K L b) := by
  apply grade_map K L _ d d
  intro s hs hsd
  rw [subdivMap_simplex K L b hs, ← hsd]
  exact subdivSimplex_degree L b s

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_LinearMapSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma linearMap_eq_of_support {K : PreAbstractSimplicialComplex V}
    {M : Type*} [AddCommMonoid M] [Module F₂ M]
    (T U : Chain K →ₗ[F₂] M) (c : Chain K)
    (hc : ∀ s ∈ c.support, T (simplex K s.val) = U (simplex K s.val)) : T c = U c := by
  rw [chain_eq_sum K c, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, map_smul, hc s hs]

lemma mapChains_boundary_simplex_of_image (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hinj), boundary_simplex L ht]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, ite_eq_right (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]

lemma mapChains_boundary_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    boundary L (mapChains K L f c) = mapChains K L f (boundary K c) := by
  apply linearMap_eq_of_support ((boundary L).comp (mapChains K L f))
    ((mapChains K L f).comp (boundary K)) c
  intro s hs
  exact mapChains_boundary_simplex_of_image K L f s.property (hc s hs)

omit [DecidableEq V] in
lemma mapChains_augmentation_simplex_of_image (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, ite_eq_left hcard, augmentation_simplex L ht, hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]

omit [DecidableEq V] in
lemma mapChains_augmentation_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    augmentation L (mapChains K L f c) = augmentation K c := by
  apply linearMap_eq_of_support ((augmentation L).comp (mapChains K L f)) (augmentation K) c
  intro s hs
  exact mapChains_augmentation_simplex_of_image K L f s.property (hc s hs)

omit [DecidableEq V] in
lemma mapChains_degree_all (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _

lemma mapChains_equivariant (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (mapChains L L d).comp (mapChains K L f) =
      (mapChains K L f).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have him : (s.val.image e).image f = (s.val.image f).image d := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun x hx => hf s.val s.property x hx)
  have hcard : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  have hcard' : ((s.val.image f).image d).card = (s.val.image f).card :=
    Finset.card_image_iff.mpr d.injective.injOn
  have hh : mapChains L L d (mapChains K L f (simplex K s.val)) =
      mapChains K L f (mapChains K K e (simplex K s.val)) := by
    rw [mapChains_simplex K L f s.property, mapChains_equiv_simplex_all K e he,
      mapChains_simplex K L f ((he s.val).mp s.property)]
    simp only [mapSimplex, him, hcard, hcard']
    split_ifs
    · exact mapChains_equiv_simplex_all L d hd _
    · exact map_zero _
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

lemma mapChains_norm (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (normMap L d).comp (mapChains K L f) =
      (mapChains K L f).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, mapChains_equivariant K L e d he hd f hf]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma flipAt_ne {n : ℕ} (b : Fin n → Bool) (i : Fin n) : flipAt b i ≠ b := by
  intro he
  have hi := congrFun he i
  simp [flipAt] at hi

lemma crossFacet_injective (n : ℕ) : Function.Injective (crossFacet n) := by
  intro b c he
  funext i
  have hi : (i.val,b i) ∈ crossFacet n c := he ▸ (mem_crossFacet n b _).mpr ⟨i,rfl⟩
  obtain ⟨j,hj⟩ := (mem_crossFacet n c _).mp hi
  have hij : i = j := Fin.ext (congrArg Prod.fst hj)
  simpa only [← hij] using congrArg Prod.snd hj

lemma mem_crossRidge (n : ℕ) (b : Fin n → Bool) (i : Fin n) (v : SignedVertex) :
    v ∈ crossRidge n b i ↔ ∃ j : Fin n, j ≠ i ∧ v = (j.val,b j) := by
  classical
  simp only [crossRidge, Finset.mem_erase, mem_crossFacet]
  constructor
  · rintro ⟨hne,j,rfl⟩
    exact ⟨j, fun h => hne (h ▸ rfl), rfl⟩
  · rintro ⟨j,hji,rfl⟩
    refine ⟨?_,j,rfl⟩
    exact fun h => hji (Fin.ext (congrArg Prod.fst h))

lemma crossRidge_subset_iff (n : ℕ) (b c : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ⊆ crossFacet n c ↔ ∀ j : Fin n, j ≠ i → c j = b j := by
  constructor
  · intro h j hji
    have hj := h ((mem_crossRidge n b i _).mpr ⟨j,hji,rfl⟩)
    obtain ⟨k,hk⟩ := (mem_crossFacet n c _).mp hj
    have hjk : j = k := Fin.ext (congrArg Prod.fst hk)
    simpa only [← hjk] using (congrArg Prod.snd hk).symm
  · intro h v hv
    obtain ⟨j,hji,rfl⟩ := (mem_crossRidge n b i v).mp hv
    exact (mem_crossFacet n c _).mpr ⟨j, by rw [h j hji]⟩

lemma crossRidge_parents (n : ℕ) (b c : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ⊆ crossFacet n c ↔ c = b ∨ c = flipAt b i := by
  rw [crossRidge_subset_iff]
  constructor
  · intro h
    by_cases hi : c i = b i
    · left
      funext j
      by_cases hj : j = i
      · subst j; exact hi
      · exact h j hj
    · right
      have hb : c i = !b i := by cases hci : c i <;> cases hbi : b i <;> simp_all
      funext j
      by_cases hj : j = i
      · subst j; simpa [flipAt] using hb
      · simpa [flipAt, hj] using h j hj
  · rintro (rfl | rfl) j hj
    · rfl
    · simp [flipAt, hj]

lemma boundary_ridge_coefficient (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n) :
    boundary (cross n) c ⟨crossRidge n b i,crossRidge_mem n hn b i⟩ =
      c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ +
      c ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩ := by
  classical
  let r : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossRidge n b i,crossRidge_mem n hn b i⟩
  let s : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩
  let t : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩
  let α : Chain (cross n) →ₗ[F₂] F₂ := Finsupp.lapply s + Finsupp.lapply t
  change ((Finsupp.lapply r).comp (boundary (cross n))) c = α c
  apply linearMap_eq_of_support
  intro a ha
  have hcard : a.val.card = n := degreeChains_card_of_ne_zero (cross n) n hc a (Finsupp.mem_support_iff.mp ha)
  obtain ⟨d,hd⟩ := cross_top_exists_signs n a.val a.property hcard
  have hcoeff := boundary_simplex_coeff (cross n) a.property r (by
    change (crossRidge n b i).card + 1 = a.val.card
    rw [crossRidge_card, hcard]
    omega)
  simp only [α, LinearMap.comp_apply, Finsupp.lapply_apply, LinearMap.add_apply]
  rw [hcoeff, simplex_coeff, simplex_coeff]
  change (if crossRidge n b i ⊆ a.val then (1:F₂) else 0) =
    (if a.val = crossFacet n b then 1 else 0) +
    (if a.val = crossFacet n (flipAt b i) then 1 else 0)
  rw [hd]
  simp only [crossRidge_parents, crossFacet_injective n |>.eq_iff]
  have hne : flipAt b i ≠ b := flipAt_ne b i
  by_cases hb : d = b <;> by_cases ht : d = flipAt b i <;> simp_all

lemma cross_cycle_adjacent_coeff (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n) (hd : boundary (cross n) c = 0) :
    c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ =
      c ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩ := by
  have h := boundary_ridge_coefficient n hn b i c hc
  rw [hd, Finsupp.zero_apply] at h
  have he := eq_neg_of_add_eq_zero_left h.symm
  simpa only [CharTwo.neg_eq] using he

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_BoolCubeConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma bool_cube_constant {n : ℕ} {A : Type*} (p : (Fin n → Bool) → A)
    (hp : ∀ b i, p b = p (flipAt b i)) (b c : Fin n → Bool) : p b = p c := by
  classical
  suffices hs : ∀ (s : Finset (Fin n)) (b c : Fin n → Bool),
      (∀ i ∉ s, b i = c i) → p b = p c by
    exact hs Finset.univ b c (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro b c h
    have he : b = c := funext (fun i => h i (by simp))
    rw [he]
  | @insert i s _ ih =>
    intro b c h
    let d := Function.update b i (c i)
    have hd : ∀ j ∉ s, d j = c j := by
      intro j hj
      by_cases he : j = i
      · subst j; simp [d]
      · simpa [d, he] using h j (by simp [hj, he])
    have he : p b = p d := by
      by_cases hb : b i = c i
      · have hbd : b = d := by
          funext j
          by_cases hji : j = i
          · subst j; simpa [d] using hb
          · simp [d, hji]
        rw [hbd]
      · have hflip : c i = !b i := by
          cases hbi : b i <;> cases hci : c i <;> simp_all
        have hdflip : d = flipAt b i := by simp only [d, flipAt, hflip]
        rw [hdflip]
        exact hp b i
    exact he.trans (ih d c hd)

lemma cross_cycle_coeff_constant (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b d : Fin n → Bool) :
    c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ =
      c ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ :=
  bool_cube_constant _ (fun b i => cross_cycle_adjacent_coeff n hn b i c hc hd) b d

lemma crossFundamental_coeff (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) :
    crossFundamental n ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ = 1 := by
  have hnonzero : crossFundamental n ≠ 0 := by
    intro h
    have hd := characteristicDegree_crossFundamental n (by omega)
    rw [h, map_zero] at hd
    exact zero_ne_one hd
  obtain ⟨s,hs⟩ : ∃ s, crossFundamental n s ≠ 0 := by
    by_contra h
    push Not at h
    exact hnonzero (Finsupp.ext h)
  have hcard : s.val.card = n := degreeChains_card_of_ne_zero (cross n) n
    (crossFundamental_degree n (by omega)) s hs
  obtain ⟨d,hd⟩ := cross_top_exists_signs n s.val s.property hcard
  have hsd : s = ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ := Subtype.ext hd
  rw [hsd] at hs
  have hconst := cross_cycle_coeff_constant n hn (crossFundamental n)
    (crossFundamental_degree n (by omega)) (crossFundamental_boundary n (by omega)) b d
  rw [hconst]
  have h₂ : ∀ x : F₂, x = 0 ∨ x = 1 := by decide
  exact (h₂ _).resolve_left hs

lemma cross_top_cycle_eq (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b : Fin n → Bool) :
    c = c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ • crossFundamental n := by
  classical
  ext s
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hcard : s.val.card = n
  · obtain ⟨d,hd'⟩ := cross_top_exists_signs n s.val s.property hcard
    have hsd : s = ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ := Subtype.ext hd'
    rw [hsd, crossFundamental_coeff n hn d, mul_one]
    exact cross_cycle_coeff_constant n hn c hc hd d b
  · have hz : c s = 0 := by
      by_contra hs
      exact hcard (degreeChains_card_of_ne_zero (cross n) n hc s hs)
    have hz' : crossFundamental n s = 0 := by
      by_contra hs
      exact hcard (degreeChains_card_of_ne_zero (cross n) n
        (crossFundamental_degree n (by omega)) s hs)
    rw [hz, hz', mul_zero]

lemma cross_characteristicDegree_eq_coeff (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b : Fin n → Bool) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) c = c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ := by
  conv_lhs => rw [cross_top_cycle_eq n hn c hc hd b]
  rw [map_smul, characteristicDegree_crossFundamental n (by omega), smul_eq_mul, mul_one]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_DoubleEraseSumFun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq W] in
lemma double_erase_sum_fun (L : PreAbstractSimplicialComplex W) (H : Finset V → Chain L)
    (s : Finset V) : (∑ a ∈ s, ∑ b ∈ s.erase a, H ((s.erase a).erase b)) = 0 := by
  classical
  let g (p : V × V) : Chain L := if p.1 = p.2 then 0 else H ((s.erase p.1).erase p.2)
  have hg : (∑ a ∈ s, ∑ b ∈ s.erase a, H ((s.erase a).erase b)) =
      ∑ p ∈ s ×ˢ s, g p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.filter_ne, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b <;> simp [g, hab, Finset.filter_ne]
  rw [hg]
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p _
    dsimp [g]
    by_cases he : p.1 = p.2
    · simp [he]
    · simp only [he, ite_false, Ne.symm he, Finset.erase_right_comm]
      exact chain_add_self L _
  · intro p _ hg he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hg (by simp [g, h])
  · intro p _; exact Prod.swap_swap p
  · intro p hp; exact Finset.mem_product.mpr (And.symm (Finset.mem_product.mp hp))

omit [DecidableEq V] in
lemma support_mapSimplex (L : PreAbstractSimplicialComplex W) (f : V → W)
    (s : Finset V) {t : {t : Finset W // t ∈ L}}
    (ht : t ∈ (mapSimplex L f s).support) : t.val = s.image f := by
  unfold mapSimplex at ht
  split_ifs at ht
  · exact (mem_support_simplex L _ t).mp ht
  · simp at ht

omit [DecidableEq V] in
lemma mapSimplex_degree (L : PreAbstractSimplicialComplex W) (f : V → W) (s : Finset V) :
    mapSimplex L f s ∈ degreeChains L s.card := by
  unfold mapSimplex
  split_ifs with h
  · rw [← h]; exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _

lemma mapSimplex_boundary (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s.image f ∈ L) :
    boundary L (mapSimplex L f s) = ∑ a ∈ s, mapSimplex L f (s.erase a) := by
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hinj), boundary_simplex L hs,
      Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr (hinj.mono (Finset.erase_subset a s))),
        image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, ite_eq_right (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]

omit [DecidableEq V] in
lemma mapSimplex_augmentation (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s.image f ∈ L) :
    augmentation L (mapSimplex L f s) = if s.card = 1 then 1 else 0 := by
  by_cases hinj : (s.image f).card = s.card
  · rw [mapSimplex, ite_eq_left hinj, augmentation_simplex L hs, hinj]
  · have hc : s.card ≠ 1 := by
      intro h
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h
      simp at hinj
    simp [mapSimplex, hinj, hc]

lemma contigSimplex_nonempty (L : PreAbstractSimplicialComplex W) (f g : V → W)
    {s : Finset V} (hs : s.Nonempty) :
    contigSimplex L f g s = cone L (f hs.choose)
      (mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a)) := by
  rw [contigSimplex, dite_eq_left hs]
  exact congrArg (fun z => cone L (f hs.choose) (mapSimplex L f s + mapSimplex L g s + z))
    (Finset.sum_attach s (fun a : V => contigSimplex L f g (s.erase a)))

lemma contigSimplex_carrier (L : PreAbstractSimplicialComplex W) (f g : V → W)
    (s : Finset V) {t : {t : Finset W // t ∈ L}}
    (ht : t ∈ (contigSimplex L f g s).support) : t.val ⊆ s.image f ∪ s.image g := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp at ht
    rw [contigSimplex_nonempty L f g hs] at ht
    obtain ⟨u,hu,_,htu⟩ := support_cone L _ _ ht
    rw [htu]
    apply Finset.insert_subset
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f hs.choose_spec)
    have hsub : ∀ a ∈ s, (s.erase a).image f ∪ (s.erase a).image g ⊆ s.image f ∪ s.image g := by
      intro a _
      exact Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
        (Finset.image_subset_image (Finset.erase_subset a s))
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · rcases Finset.mem_union.mp (Finsupp.support_add hu) with hf | hg
      · rw [support_mapSimplex L f s hf]; exact Finset.subset_union_left
      · rw [support_mapSimplex L g s hg]; exact Finset.subset_union_right
    · obtain ⟨a,ha,hua⟩ := support_sum_chains L s _ hu
      exact (ih (s.erase a) (Finset.erase_ssubset ha) hua).trans (hsub a ha)

lemma contigSimplex_degree (L : PreAbstractSimplicialComplex W) (f g : V → W)
    (s : Finset V) : contigSimplex L f g s ∈ degreeChains L (s.card+1) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [contigSimplex_empty]; exact Submodule.zero_mem _
    rw [contigSimplex_nonempty L f g hs]
    apply cone_degree L _ s.card
    apply Submodule.add_mem _
    · exact Submodule.add_mem _ (mapSimplex_degree L f s) (mapSimplex_degree L g s)
    · apply Submodule.sum_mem
      intro a ha
      have h := ih (s.erase a) (Finset.erase_ssubset ha)
      simpa only [Finset.card_erase_of_mem ha, Nat.sub_add_cancel hs.card_pos] using h

lemma contigSimplex_augmentation (L : PreAbstractSimplicialComplex W) (f g : V → W)
    (s : Finset V) : augmentation L (contigSimplex L f g s) = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  exact augmentation_eq_zero_of_degree L (s.card+1) (by have := hs.card_pos; omega)
    (contigSimplex_degree L f g s)

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_ContigSimplexBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma contigSimplex_boundary (L : PreAbstractSimplicialComplex W) (f g : V → W)
    {s : Finset V} (hs : s.image f ∪ s.image g ∈ L) :
    boundary L (contigSimplex L f g s) =
      mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn : s.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      have hs' : (∅ : Finset W) ∈ L := by simpa [he] using hs
      simpa using (L.isRelLowerSet_faces hs').1
    have hf : s.image f ∈ L := (L.isRelLowerSet_faces hs).2 Finset.subset_union_left (hn.image f)
    have hg : s.image g ∈ L := (L.isRelLowerSet_faces hs).2 Finset.subset_union_right (hn.image g)
    have hb : f hn.choose ∈ s.image f ∪ s.image g :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem f hn.choose_spec)
    let z := mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a)
    have hi (a : V) (ha : a ∈ s) : boundary L (contigSimplex L f g (s.erase a)) =
        mapSimplex L f (s.erase a) + mapSimplex L g (s.erase a) +
          ∑ b ∈ s.erase a, contigSimplex L f g ((s.erase a).erase b) := by
      rcases (s.erase a).eq_empty_or_nonempty with he | hne
      · simp [he, mapSimplex]
      · apply ih (s.erase a) (Finset.erase_ssubset ha)
        apply (L.isRelLowerSet_faces hs).2
        · exact Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
            (Finset.image_subset_image (Finset.erase_subset a s))
        · exact (hne.image f).mono Finset.subset_union_left
    have hzbd : boundary L z = 0 := by
      simp only [z, map_add, map_sum, mapSimplex_boundary L f hf, mapSimplex_boundary L g hg]
      rw [Finset.sum_congr rfl hi]
      simp only [Finset.sum_add_distrib]
      rw [double_erase_sum_fun, add_zero]
      exact chain_add_self L _
    have hzaug : augmentation L z = 0 := by
      simp only [z, map_add, map_sum, mapSimplex_augmentation L f hf,
        mapSimplex_augmentation L g hg, contigSimplex_augmentation, Finset.sum_const_zero, add_zero]
      exact CharTwo.add_self_eq_zero _
    have hzcone : ∀ t ∈ z.support, insert (f hn.choose) t.val ∈ L := by
      intro t ht
      apply (L.isRelLowerSet_faces hs).2 _ (Finset.insert_nonempty _ _)
      apply Finset.insert_subset hb
      rcases Finset.mem_union.mp (Finsupp.support_add ht) with ht | ht
      · rcases Finset.mem_union.mp (Finsupp.support_add ht) with htf | htg
        · rw [support_mapSimplex L f s htf]; exact Finset.subset_union_left
        · rw [support_mapSimplex L g s htg]; exact Finset.subset_union_right
      · obtain ⟨a,ha,hta⟩ := support_sum_chains L s _ ht
        exact (contigSimplex_carrier L f g (s.erase a) hta).trans
          (Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
            (Finset.image_subset_image (Finset.erase_subset a s)))
    rw [contigSimplex_nonempty L f g hn]
    change boundary L (cone L (f hn.choose) z) = z
    rw [cone_boundary L _ z hzcone, hzbd, hzaug, map_zero, zero_smul, add_zero, add_zero]

lemma contigMap_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) {s : Finset V} (hs : s ∈ K) :
    contigMap K L f g (simplex K s) = contigSimplex L f g s := by
  simp [simplex_of_mem K hs, contigMap, Finsupp.linearCombination_single]

lemma contigMap_simplex_subset (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) :
    contigMap K L f g (simplex K s) = contigSimplex L f g s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact contigMap_simplex K L f g ((K.isRelLowerSet_faces ht).2 hs hn)

lemma contigMap_degree (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L (d+1)).comap (contigMap K L f g) := by
  apply grade_map K L _ d (d+1)
  intro s hs hd
  rw [contigMap_simplex K L f g hs, ← hd]
  exact contigSimplex_degree L f g s

lemma contigMap_boundary_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∪ s.val.image g ∈ L) :
    boundary L (contigMap K L f g c) = mapChains K L f c + mapChains K L g c +
      contigMap K L f g (boundary K c) := by
  let A : Chain K →ₗ[F₂] Chain L :=
    mapChains K L f + mapChains K L g + (contigMap K L f g).comp (boundary K)
  change ((boundary L).comp (contigMap K L f g)) c = A c
  apply linearMap_eq_of_support
  intro s hs
  simp only [LinearMap.comp_apply, A, LinearMap.add_apply]
  rw [contigMap_simplex K L f g s.property, contigSimplex_boundary L f g (hc s hs),
    mapChains_simplex K L f s.property, mapChains_simplex K L g s.property,
    boundary_simplex K s.property, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact (contigMap_simplex_subset K L f g s.property (Finset.erase_subset a s.val)).symm

lemma contig_maps_agree_top (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f g : V → W) (d : ℕ) (c : Chain K)
    (hc : c ∈ degreeChains K d) (hbd : boundary K c = 0)
    (hfg : ∀ s ∈ c.support, s.val.image f ∪ s.val.image g ∈ L)
    (hL : ∀ s ∈ L, s.card ≤ d) : mapChains K L f c = mapChains K L g c := by
  have hh : contigMap K L f g c = 0 := by
    have ht := contigMap_degree K L f g d hc
    rw [degreeChains_eq_bot_of_card_bound L (d+1) (fun s hs => by have := hL s hs; omega)] at ht
    exact ht
  have he := contigMap_boundary_of_support K L f g c hfg
  rw [hh, map_zero, hbd, map_zero, add_zero] at he
  have h := eq_neg_of_add_eq_zero_left he.symm
  have hn : -(mapChains K L g c) = mapChains K L g c := by
    ext s
    exact CharTwo.neg_eq _
  exact h.trans hn

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CrossChainDimensionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma barycenter_eq_centerMass (s : Finset E) :
    barycenter s = s.centerMass (fun _ => (1 : ℝ)) id := by
  simp [barycenter, Finset.centerMass]

lemma barycenter_mem_convex {A : Set E} (hA : Convex ℝ A) {s : Finset E}
    (hs : s.Nonempty) (hsA : (s : Set E) ⊆ A) : barycenter s ∈ A := by
  rw [barycenter_eq_centerMass]
  apply hA.centerMass_mem
  · intro x hx; exact zero_le_one
  · simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card)
  · intro x hx; exact hsA hx

lemma barycenter_norm_le {s : Finset E} (hs : s.Nonempty) {D : ℝ}
    (hD : ∀ x ∈ s, ‖x‖ ≤ D) : ‖barycenter s‖ ≤ D := by
  have h := barycenter_mem_convex (convex_closedBall (0 : E) D) hs (A := Metric.closedBall 0 D)
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hD x hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

lemma barycenter_inner {s : Finset E} (hs : s.Nonempty) (w : E)
    (hw : ∀ x ∈ s, ⟪w,x⟫ = 1) : ⟪w,barycenter s⟫ = 1 := by
  rw [barycenter, real_inner_smul_right, inner_sum]
  simp only [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero)

lemma barycenter_sub_eq {s : Finset E} (hs : s.Nonempty) (x : E) :
    barycenter s - x = (s.card : ℝ)⁻¹ • ∑ y ∈ s, (y-x) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero), one_smul]
  rfl

lemma barycenter_dist_vertex [DecidableEq E] {s : Finset E} {x : E} (hx : x ∈ s)
    {D : ℝ} (hD : ∀ y ∈ s, ∀ z ∈ s, dist y z ≤ D) :
    dist (barycenter s) x ≤ ((s.card : ℝ)-1) / s.card * D := by
  have hs : s.Nonempty := ⟨x,hx⟩
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [dist_eq_norm, barycenter_sub_eq hs x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  have hh : (∑ y ∈ s, (y-x)) = ∑ y ∈ s.erase x, (y-x) := by
    rw [← Finset.sum_erase_add _ _ hx]
    simp
  rw [hh]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ y ∈ s.erase x, (y-x)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, ‖y-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt hc))
    _ ≤ (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, D := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hc))
      apply Finset.sum_le_sum
      intro y hy
      simpa only [dist_eq_norm] using hD y (Finset.mem_of_mem_erase hy) x hx
    _ = ((s.card : ℝ)-1) / s.card * D := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hx,
        Nat.cast_sub hs.card_pos, Nat.cast_one]
      ring

lemma barycenter_dist_carrier [DecidableEq E] {s t : Finset E} (ht : t.Nonempty)
    (hts : t ⊆ s) {D : ℝ} (hD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D) :
    dist (barycenter s) (barycenter t) ≤ ((s.card : ℝ)-1) / s.card * D := by
  have h := barycenter_mem_convex
    (convex_closedBall (barycenter s) (((s.card : ℝ)-1) / s.card * D)) ht
    (fun x hx => (Metric.mem_closedBall').mpr (barycenter_dist_vertex (hts hx) hD))
  exact (Metric.mem_closedBall').mp h

lemma barycenter_mesh_factor {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    ((a : ℝ)-1) / a ≤ ((n : ℝ)-1) / n := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le ha han
  apply (div_le_div_iff₀ ha' hn').mpr
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  nlinarith

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_BarycenterNeg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]

lemma barycenter_neg (s : Finset E) : barycenter (s.image Neg.neg) = -barycenter s := by
  rw [barycenter, Finset.card_image_iff.mpr neg_injective.injOn,
    Finset.sum_image neg_injective.injOn, Finset.sum_neg_distrib,
    smul_neg, barycenter]

lemma hemisphere_neg (R : ℝ) (s : Finset E) :
    s ∈ hemisphereComplex R ↔ s.image Neg.neg ∈ hemisphereComplex R := by
  constructor
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨hn.image _, -w, by simpa using hw, ?_⟩
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa using hh y hy
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨Finset.image_nonempty.mp hn, -w, by simpa using hw, ?_⟩
    intro x hx
    have h := hh (-x) (Finset.mem_image_of_mem Neg.neg hx)
    simpa using h

omit [DecidableEq E] in
lemma hemisphere_subdivision_carrier (R : ℝ) :
    SubdivisionCarrier (hemisphereComplex R : PreAbstractSimplicialComplex E)
      (hemisphereComplex R) barycenter := by
  rintro s ⟨hn,w,hw,hh⟩ t ht hts
  refine ⟨ht,w,hw,?_⟩
  intro x hx
  obtain ⟨u,hu,hus,rfl⟩ := hts hx
  exact ⟨barycenter_norm_le hu (fun y hy => (hh y (hus hy)).1),
    barycenter_inner hu w (fun y hy => (hh y (hus hy)).2)⟩

lemma subdivSimplex_mesh (R : ℝ) (s : Finset E) (n : ℕ) (hsn : s.card ≤ n)
    (D : ℝ) (hD : 0 ≤ D) (hsD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (subdivSimplex (hemisphereComplex R) barycenter s).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ ((n : ℝ)-1) / n * D := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    have hfac : 0 ≤ ((n : ℝ)-1) / n := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hn.card_pos hsn
      exact div_nonneg (by linarith) (by positivity)
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one _ _ hc, mem_support_simplex] at ht
      intro x hx y hy
      rw [ht, Finset.mem_singleton] at hx hy
      subst x; subst y
      simpa only [dist_self] using mul_nonneg hfac hD
    · rw [subdivSimplex_many _ _ hn hc] at ht
      obtain ⟨u,hu,_,htu⟩ := support_cone _ (barycenter s) _ ht
      obtain ⟨a,ha,hua⟩ := support_sum_chains _ s _ hu
      have hsmall := ih (s.erase a) (Finset.erase_ssubset ha)
        (le_trans (Finset.card_le_card (Finset.erase_subset a s)) hsn)
        (fun x hx y hy => hsD x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)) hua
      have hcarrier := (subdivSimplex_carrier _ barycenter _ hua).trans
        (vertexCarrier_mono barycenter (Finset.erase_subset a s))
      have hcenter (x : E) (hx : x ∈ u.val) :
          dist (barycenter s) x ≤ ((n : ℝ)-1) / n * D := by
        obtain ⟨v,hv,hvs,rfl⟩ := hcarrier hx
        exact (barycenter_dist_carrier hv hvs hsD).trans
          (mul_le_mul_of_nonneg_right (barycenter_mesh_factor hn.card_pos hsn) hD)
      intro x hx y hy
      rw [htu, Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · simpa only [dist_self] using mul_nonneg hfac hD
      · exact hcenter y hy
      · rw [dist_comm]; exact hcenter x hx
      · exact hsmall x hx y hy

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CrossEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma crossEmbedding_norm (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ‖crossEmbedding n v‖ = 1 := by
  simp only [crossEmbedding, dite_eq_left hv, norm_smul, PiLp.norm_single]
  cases v.2 <;> norm_num

lemma crossEmbedding_flip (n : ℕ) (v : SignedVertex) :
    crossEmbedding n (flip v) = -crossEmbedding n v := by
  rcases v with ⟨i,b⟩
  cases b <;> simp only [crossEmbedding, flip_apply] <;> split_ifs <;> simp_all

lemma crossEmbedding_inner_ne (n : ℕ) {v w : SignedVertex}
    (hvw : v.1 ≠ w.1) : ⟪crossEmbedding n v, crossEmbedding n w⟫ = 0 := by
  unfold crossEmbedding
  split_ifs <;> simp_all [EuclideanSpace.inner_single_left]

lemma crossEmbedding_inner_self (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ⟪crossEmbedding n v, crossEmbedding n v⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, crossEmbedding_norm n v hv]
  norm_num

lemma crossEmbedding_face (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image (crossEmbedding n) ∈ hemisphereComplex (n:ℝ) := by
  refine ⟨hs.1.image _, ∑ v ∈ s, crossEmbedding n v, ?_, ?_⟩
  · calc
      ‖∑ v ∈ s, crossEmbedding n v‖ ≤ ∑ v ∈ s, ‖crossEmbedding n v‖ := norm_sum_le _ _
      _ = s.card := by simp only [Finset.sum_congr rfl (fun v hv => crossEmbedding_norm n v (hs.2.1 v hv)), Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (n:ℝ) := by exact_mod_cast cross_card n s hs
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨le_of_eq (crossEmbedding_norm n v (hs.2.1 v hv)), ?_⟩
    rw [sum_inner, Finset.sum_eq_single v]
    · exact crossEmbedding_inner_self n v (hs.2.1 v hv)
    · intro w hw hwv
      exact crossEmbedding_inner_ne n (fun he => hwv (hs.2.2 hw hv he))
    · exact fun hn => False.elim (hn hv)

lemma crossGeometricMap_boundary (n : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (boundary (cross n)) :=
  mapChains_boundary _ _ _ (crossEmbedding_face n)

lemma crossGeometricMap_augmentation (n : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      augmentation (cross n) := mapChains_augmentation _ _ _ (crossEmbedding_face n)

lemma crossGeometricMap_degree (n d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (crossGeometricMap n) := mapChains_degree _ _ _ (crossEmbedding_face n) d

lemma crossGeometricMap_norm (n : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (normMap (cross n) flip) := by
  apply mapChains_norm _ _ flip (Equiv.neg _) (cross_flip n) (hemisphere_neg (n:ℝ))
  intro s hs x hx
  exact crossEmbedding_flip n x

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MaxIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma maxIndex_le {m : ℕ} [NeZero m] (g : Fin m → ℝ) (i : Fin m) :
    g i ≤ g (maxIndex g) :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose_spec.2 i (Finset.mem_univ _)

lemma peakIndex_neg {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) :
    peakIndex (-y) = peakIndex y := by
  unfold peakIndex
  congr 1
  ext i
  simp

lemma euclidean_norm_le_sum_abs {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ‖y‖ ≤ ∑ i, |y i| := by
  have hy : y = ∑ i, EuclideanSpace.single i (y i) := by
    ext i
    simp
  calc
    ‖y‖ = ‖∑ i, EuclideanSpace.single i (y i)‖ := congrArg norm hy
    _ ≤ ∑ i, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
    _ = ∑ i, |y i| := by simp

lemma peak_large {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    (1:ℝ) / m ≤ |y (peakIndex y)| := by
  have h := euclidean_norm_le_sum_abs y
  rw [hy] at h
  have hsum : ∑ i : Fin m, |y i| ≤ (m:ℝ) * |y (peakIndex y)| := by
    calc
      ∑ i : Fin m, |y i| ≤ ∑ _ : Fin m, |y (peakIndex y)| :=
        Finset.sum_le_sum (fun i _ => maxIndex_le (fun j => |y j|) i)
      _ = _ := by simp
  exact (div_le_iff₀ (by exact_mod_cast NeZero.pos m)).mpr (by nlinarith)

lemma sphereLabel_bound {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) :
    (sphereLabel y).1 < m := (peakIndex y).isLt

lemma sphereLabel_neg {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    sphereLabel (-y) = flip (sphereLabel y) := by
  have hpeak : y (peakIndex y) ≠ 0 := by
    have h := peak_large y hy
    have hm : (0:ℝ) < (1:ℝ)/m := div_pos zero_lt_one (by exact_mod_cast NeZero.pos m)
    intro he
    rw [he, abs_zero] at h
    linarith
  apply Prod.ext
  · simp only [sphereLabel, peakIndex_neg, flip_apply]
  · simp only [sphereLabel, peakIndex_neg, flip_apply, PiLp.neg_apply]
    by_cases h : y (peakIndex y) < 0
    · have h' : ¬ -y (peakIndex y) < 0 := by linarith
      simp [h,h']
    · have h' : -y (peakIndex y) < 0 := by rcases lt_or_gt_of_ne hpeak with hn | hp <;> linarith
      simp [h,h']

lemma sphereLabel_compatible {m : ℕ} [NeZero m]
    (y z : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hd : dist y z < (1:ℝ)/m) (hi : (sphereLabel y).1 = (sphereLabel z).1) :
    sphereLabel y = sphereLabel z := by
  have he : peakIndex y = peakIndex z := Fin.ext hi
  have hcoord : |y (peakIndex y) - z (peakIndex y)| ≤ dist y z := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le y z (peakIndex y)
  have hym := peak_large y hy
  have hzm := peak_large z hz
  rw [← he] at hzm
  apply Prod.ext hi
  change decide (y (peakIndex y) < 0) = decide (z (peakIndex z) < 0)
  rw [← he]
  congr 1
  apply propext
  constructor
  · intro hyneg
    by_contra hzneg
    have hzpos := le_of_not_gt hzneg
    rw [abs_of_neg hyneg] at hym
    rw [abs_of_nonpos (by linarith)] at hcoord
    linarith
  · intro hzneg
    by_contra hyneg
    have hypos := le_of_not_gt hyneg
    rw [abs_of_neg hzneg] at hzm
    rw [abs_of_nonneg (by linarith)] at hcoord
    linarith

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]

lemma refinement_boundary (R : ℝ) (r : ℕ) :
    (boundary (hemisphereComplex R : PreAbstractSimplicialComplex E)).comp (refinement R r) =
      (refinement R r).comp (boundary (hemisphereComplex R)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc, subdivMap_boundary _ _ _ (hemisphere_subdivision_carrier R),
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

lemma refinement_augmentation (R : ℝ) (r : ℕ) :
    (augmentation (hemisphereComplex R : PreAbstractSimplicialComplex E)).comp
      (refinement R r) = augmentation (hemisphereComplex R) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_augmentation _ _ _ (hemisphere_subdivision_carrier R), ih]

lemma refinement_norm (R : ℝ) (r : ℕ) :
    (normMap (hemisphereComplex R : PreAbstractSimplicialComplex E) (Equiv.neg E)).comp
      (refinement R r) = (refinement R r).comp (normMap (hemisphereComplex R) (Equiv.neg E)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_norm _ _ (Equiv.neg E) (Equiv.neg E) (hemisphere_neg R) (hemisphere_neg R)
        barycenter (barycenter_neg), LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

lemma refinement_degree (R : ℝ) (r d : ℕ) :
    degreeChains (hemisphereComplex R : PreAbstractSimplicialComplex E) d ≤
      (degreeChains (hemisphereComplex R) d).comap (refinement R r) := by
  induction r with
  | zero => intro c hc; exact hc
  | succ r ih =>
    intro c hc
    change subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c) ∈ degreeChains (hemisphereComplex R) d
    exact subdivMap_degree (hemisphereComplex R : PreAbstractSimplicialComplex E)
      (hemisphereComplex R) barycenter d (ih hc)

lemma refinement_mesh (R : ℝ) (r n : ℕ) {c : Chain (hemisphereComplex R : PreAbstractSimplicialComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) n) {D : ℝ} (hD : 0 ≤ D)
    (hmesh : ∀ s ∈ c.support, ∀ x ∈ s.val, ∀ y ∈ s.val, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * D := by
  induction r generalizing t with
  | zero => simpa only [refinement, LinearMap.id_apply, pow_zero, one_mul] using hmesh t ht
  | succ r ih =>
    change t ∈ (subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c)).support at ht
    obtain ⟨s,hs,hts⟩ := support_linearMap _ _ _ _ ht
    rw [subdivMap_simplex _ _ _ s.property] at hts
    have hdeg := refinement_degree R r n hc hs
    change s.val.card = n at hdeg
    have hn : 0 < n := hdeg ▸ s.property.1.card_pos
    have hfac : 0 ≤ ((n:ℝ)-1)/n := by
      have hh : (1:ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg (by linarith) (by positivity)
    have hh := subdivSimplex_mesh R s.val n (le_of_eq hdeg)
      ((((n:ℝ)-1)/n)^r * D) (mul_nonneg (pow_nonneg hfac _) hD) (ih hs) hts
    simpa only [pow_succ', mul_assoc] using hh

omit [DecidableEq E] in
lemma hemisphere_mesh_two (R : ℝ) {s : Finset E} (hs : s ∈ hemisphereComplex R)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ 2 := by
  obtain ⟨_, _, _, unit_norm⟩ := hs
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 2 := by linarith [(unit_norm x hx).1, (unit_norm y hy).1]

lemma refinement_mesh_uniform (R : ℝ) (r n d : ℕ) (hd : d ≤ n)
    {c : Chain (hemisphereComplex R : PreAbstractSimplicialComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) d)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  have hdeg := refinement_degree R r d hc ht
  have htpos := t.property.1.card_pos
  change t.val.card = d at hdeg
  have hdpos : 0 < d := hdeg ▸ htpos
  have hfac : 0 ≤ ((d:ℝ)-1)/d := by
    have hh : (1:ℝ) ≤ d := by exact_mod_cast hdpos
    exact div_nonneg (by linarith) (by positivity)
  have hm := refinement_mesh R r d hc (D := 2) (by norm_num)
    (fun simplex _ _ first_mem _ second_mem =>
      hemisphere_mesh_two R simplex.property first_mem second_mem) ht
  intro x hx y hy
  exact (hm x hx y hy).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hfac (barycenter_mesh_factor hdpos hd) r) (by norm_num))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_FineCrossMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma fineCrossMap_boundary (n r : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (boundary (cross n)) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_boundary,
    LinearMap.comp_assoc, crossGeometricMap_boundary, ← LinearMap.comp_assoc]

lemma fineCrossMap_augmentation (n r : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) = augmentation (cross n) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_augmentation,
    crossGeometricMap_augmentation]

lemma fineCrossMap_norm (n r : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (normMap (cross n) flip) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_norm,
    LinearMap.comp_assoc, crossGeometricMap_norm, ← LinearMap.comp_assoc]

lemma fineCrossMap_degree (n r d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (fineCrossMap n r) := by
  intro c hc
  change refinement (n:ℝ) r (crossGeometricMap n c) ∈ degreeChains (hemisphereComplex (n:ℝ)) d
  exact refinement_degree (E := EuclideanSpace ℝ (Fin n)) (n:ℝ) r d
    (crossGeometricMap_degree n d hc)

lemma fineCrossMap_simplex_mesh (n r : ℕ) {s : Finset SignedVertex} (hs : s ∈ cross n)
    {t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  apply refinement_mesh_uniform (n:ℝ) r n s.card (cross_card n s hs)
    (crossGeometricMap_degree n s.card (simplex_mem_degree _ hs)) ht

lemma annulus_compact (n : ℕ) : IsCompact (annulus n) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2

lemma hemisphere_vertex_annulus (n : ℕ) (hn : 0 < n)
    {s : Finset (EuclideanSpace ℝ (Fin n))} (hs : s ∈ hemisphereComplex (n:ℝ))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) : x ∈ annulus n := by
  obtain ⟨_,w,hw,hh⟩ := hs
  refine ⟨?_,(hh x hx).1⟩
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  have h := real_inner_le_norm w x
  rw [(hh x hx).2] at h
  calc
    1 ≤ ‖w‖ * ‖x‖ := h
    _ ≤ (n:ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg x)
    _ = ‖x‖ * (n:ℝ) := mul_comm _ _

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma approximation_boundary (n m r : ℕ) (f : EuclideanSpace ℝ (Fin n) → SignedVertex)
    (hf : IsFineLabel n m r f) :
    (boundary (cross m)).comp (approximation n m r f) =
      (approximation n m r f).comp (boundary (cross n)) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : boundary (cross m) (approximation n m r f (simplex (cross n) s.val)) =
      approximation n m r f (boundary (cross n) (simplex (cross n) s.val)) := by
    change boundary (cross m) (mapChains (hemisphereComplex (n:ℝ)) (cross m) f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_boundary_of_support _ (cross m) f _ (hf s.val s.property)]
    have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
    rw [hb]
    rfl
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]

lemma approximation_augmentation (n m r : ℕ) (f : EuclideanSpace ℝ (Fin n) → SignedVertex)
    (hf : IsFineLabel n m r f) :
    (augmentation (cross m)).comp (approximation n m r f) = augmentation (cross n) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : augmentation (cross m) (approximation n m r f (simplex (cross n) s.val)) =
      augmentation (cross n) (simplex (cross n) s.val) := by
    change augmentation (cross m) (mapChains (hemisphereComplex (n:ℝ)) (cross m) f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_augmentation_of_support _ (cross m) f _ (hf s.val s.property)]
    exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]

lemma approximation_norm (n m r : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → SignedVertex)
    (hf : ∀ x ∈ annulus n, f (-x) = flip (f x)) :
    (normMap (cross m) flip).comp (approximation n m r f) =
      (approximation n m r f).comp (normMap (cross n) flip) := by
  have hu : (normMap (cross m) flip).comp (mapChains (hemisphereComplex (n:ℝ)) (cross m) f) =
      (mapChains (hemisphereComplex (n:ℝ)) (cross m) f).comp
        (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)) := by
    apply mapChains_norm _ (cross m) (Equiv.neg _) flip (hemisphere_neg (n:ℝ)) (cross_flip m) f
    intro s hs x hx
    exact hf x (hemisphere_vertex_annulus n hn hs hx)
  rw [approximation, ← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
    fineCrossMap_norm, ← LinearMap.comp_assoc]

lemma approximation_degree (n m r d : ℕ) (f : EuclideanSpace ℝ (Fin n) → SignedVertex) :
    degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap (approximation n m r f) := by
  intro c hc
  exact mapChains_degree_all _ (cross m) f d (fineCrossMap_degree n r d hc)

lemma cross_equivariant_fundamental (n : ℕ) (hn : 1 < n)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross n))
    (hTbd : (boundary (cross n)).comp T = T.comp (boundary (cross n)))
    (hTN : (normMap (cross n) flip).comp T = T.comp (normMap (cross n) flip))
    (hTa : (augmentation (cross n)).comp T = augmentation (cross n))
    (hTd : ∀ c ∈ degreeChains (cross n) n, T c ∈ degreeChains (cross n) n) :
    T (crossFundamental n) = crossFundamental n := by
  have hc := hTd _ (crossFundamental_degree n (by omega))
  have hb : boundary (cross n) (T (crossFundamental n)) = 0 := by
    rw [← LinearMap.comp_apply, hTbd, LinearMap.comp_apply,
      crossFundamental_boundary n (by omega), map_zero]
  have hd : T (crossFundamental n) ⟨crossFacet n (fun _ => false),
      crossFacet_mem n (by omega) (fun _ => false)⟩ = 1 := by
    rw [← cross_characteristicDegree_eq_coeff n hn _ hc hb]
    exact cross_equivariant_degree_one n (by omega) T hTbd hTN hTa
  rw [cross_top_cycle_eq n hn _ hc hb (fun _ => false), hd, one_smul]

lemma approximation_odd_fundamental (n r : ℕ) (hn : 1 < n)
    (f : EuclideanSpace ℝ (Fin n) → SignedVertex) (hf : IsFineLabel n n r f)
    (ho : ∀ x ∈ annulus n, f (-x) = flip (f x)) :
    approximation n n r f (crossFundamental n) = crossFundamental n := by
  apply cross_equivariant_fundamental n hn _ (approximation_boundary n n r f hf)
    (approximation_norm n n r (by omega) f ho) (approximation_augmentation n n r f hf)
  intro c hc
  exact approximation_degree n n r n f hc

lemma approximation_agree_top (n m r : ℕ) (hn : 0 < n)
    (f g : EuclideanSpace ℝ (Fin n) → SignedVertex)
    (hcard : m ≤ n)
    (hfg : ∀ s ∈ (fineCrossMap n r (crossFundamental n)).support,
      s.val.image f ∪ s.val.image g ∈ cross m) :
    approximation n m r f (crossFundamental n) = approximation n m r g (crossFundamental n) := by
  apply contig_maps_agree_top _ (cross m) f g n _
    (fineCrossMap_degree n r n (crossFundamental_degree n hn)) _ hfg
    (fun s hs => (cross_card m s hs).trans hcard)
  rw [← LinearMap.comp_apply, fineCrossMap_boundary, LinearMap.comp_apply,
    crossFundamental_boundary n hn, map_zero]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_FineCrossMapMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped Topology

lemma fineCrossMap_mesh (n r : ℕ) (c : Chain (cross n))
    {t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  obtain ⟨s,_,ht⟩ := support_linearMap (cross n) (hemisphereComplex (n:ℝ)) _ c ht
  exact fineCrossMap_simplex_mesh n r s.property ht

lemma cross_union_labels_mem {m : ℕ} [NeZero m] {V : Type*} [DecidableEq V]
    (s : Finset V) (hs : s.Nonempty) (f g : V → EuclideanSpace ℝ (Fin m))
    (hn : ∀ x ∈ s, ‖f x‖ = 1 ∧ ‖g x‖ = 1)
    (hclose : ∀ x ∈ s, ∀ y ∈ s,
      dist (f x) (f y) < (1:ℝ)/m ∧ dist (f x) (g y) < (1:ℝ)/m ∧
      dist (g x) (f y) < (1:ℝ)/m ∧ dist (g x) (g y) < (1:ℝ)/m) :
    s.image (fun x => sphereLabel (f x)) ∪ s.image (fun x => sphereLabel (g x)) ∈ cross m := by
  refine ⟨(hs.image _).mono Finset.subset_union_left, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hf | hg <;>
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ‹_› <;> exact sphereLabel_bound _
  · intro v hv w hw he
    rcases Finset.mem_union.mp hv with hf | hg <;>
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ‹_› <;>
      rcases Finset.mem_union.mp hw with hff | hgg <;>
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ‹_›
    · exact sphereLabel_compatible _ _ (hn x hx).1 (hn y hy).1 (hclose x hx y hy).1 he
    · exact sphereLabel_compatible _ _ (hn x hx).1 (hn y hy).2 (hclose x hx y hy).2.1 he
    · exact sphereLabel_compatible _ _ (hn x hx).2 (hn y hy).1 (hclose x hx y hy).2.2.1 he
    · exact sphereLabel_compatible _ _ (hn x hx).2 (hn y hy).2 (hclose x hx y hy).2.2.2 he

lemma sphere_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHn : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, ‖H p‖ = 1) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ u ∈ Set.Icc (0:ℝ) 1,
      approximation n m r (fun x => sphereLabel (H (t,x))) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (H (u,x))) (crossFundamental n) := by
  classical
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := isCompact_Icc.prod (annulus_compact n)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hH) ((1:ℝ)/m)
      (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let C : Set.Icc (0:ℝ) 1 → Chain (cross m) :=
    fun t => approximation n m r (fun x => sphereLabel (H (t.val,x))) (crossFundamental n)
  have hClocal : IsLocallyConstant C := by
    apply (IsLocallyConstant.iff_eventually_eq C).mpr
    intro t
    filter_upwards [Metric.ball_mem_nhds t hδ] with u hu
    apply approximation_agree_top n m r hn _ _ hmn
    intro s hs
    have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
    have ha : ∀ x ∈ s.val, x ∈ annulus n :=
      fun x hx => hemisphere_vertex_annulus n hn s.property hx
    have hh (v w : Set.Icc (0:ℝ) 1) (hv : dist v.val w.val < δ)
        (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ s.val)
        (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ s.val) :
        dist (H (v.val,x)) (H (w.val,y)) < (1:ℝ)/m := by
      apply hclose (v.val,x) ⟨v.property,ha x hx⟩ (w.val,y) ⟨w.property,ha y hy⟩
      rw [Prod.dist_eq]
      exact max_lt hv ((hmesh x hx y hy).trans_lt hr)
    have hut : dist u.val t.val < δ := hu
    have htu : dist t.val u.val < δ := by simpa only [dist_comm] using hut
    apply cross_union_labels_mem s.val s.property.1 _ _
    · intro x hx
      exact ⟨hHn (u.val,x) ⟨u.property,ha x hx⟩,hHn (t.val,x) ⟨t.property,ha x hx⟩⟩
    · intro x hx y hy
      exact ⟨hh u u (by simpa using hδ) x hx y hy,hh u t hut x hx y hy,
        hh t u htu x hx y hy,hh t t (by simpa using hδ) x hx y hy⟩
  let : PreconnectedSpace (Set.Icc (0:ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  intro t ht u hu
  exact hClocal.apply_eq_of_preconnectedSpace ⟨t,ht⟩ ⟨u,hu⟩

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_UnitRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma unitRadial_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : ‖unitRadial x‖ = 1 := by
  rw [unitRadial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma unitRadial_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    unitRadial (-x) = -unitRadial x := by simp [unitRadial]

lemma unitRadial_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : ∀ x ∈ S, x ≠ 0) : ContinuousOn unitRadial S := by
  exact (continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr (hS x hx))).smul
    continuous_id.continuousOn

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_EventuallyFineSphereLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma eventually_fine_sphereLabel (n m : ℕ) (hn : 0 < n) [NeZero m]
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ → IsFineLabel n m r (fun x => sphereLabel (g x)) := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((annulus_compact n).uniformContinuousOn_of_continuous hg) ((1:ℝ)/m)
      (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  refine ⟨δ,hδ,?_⟩
  intro r hr s hs t ht
  refine ⟨t.property.1.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact sphereLabel_bound _
  · intro v hv w hw he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    have hx' := hemisphere_vertex_annulus n hn t.property hx
    have hy' := hemisphere_vertex_annulus n hn t.property hy
    exact sphereLabel_compatible _ _ (hgn x hx') (hgn y hy')
      (hclose x hx' y hy' ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hr)) he

lemma eventually_odd_sphere_degree (n : ℕ) (hn : 1 < n) [NeZero n]
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) = crossFundamental n := by
  obtain ⟨δ,hδ,hr⟩ := eventually_fine_sphereLabel n n (by omega) g hg hgn
  refine ⟨δ,hδ,fun r hh => approximation_odd_fundamental n r hn _ (hr r hh) ?_⟩
  intro x hx
  rw [hgo x hx,sphereLabel_neg _ (hgn x hx)]

lemma normalized_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (unitRadial (H (0,x)))) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (unitRadial (H (1,x)))) (crossFundamental n) := by
  obtain ⟨δ,hδ,hh⟩ := sphere_homotopy_chains n m hn hmn (fun p => unitRadial (H p))
    ((unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp hH hHz)
    (fun p hp => unitRadial_norm (hHz p hp))
  exact ⟨δ,hδ,fun r hr => hh r hr 0 ⟨le_rfl,zero_le_one⟩ 1 ⟨zero_le_one,le_rfl⟩⟩

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_LabelRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma labelRegion_closed {m : ℕ} (i : Fin m) (b : Bool) : IsClosed (labelRegion i b) := by
  have hc (j : Fin m) : Continuous (fun y : EuclideanSpace ℝ (Fin m) => y j) :=
    PiLp.continuous_apply 2 _ j
  apply IsClosed.inter
  · change IsClosed {y : EuclideanSpace ℝ (Fin m) | ∀ j, |y j| ≤ |y i|}
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (hc j).abs (hc i).abs)
  · cases b
    · exact isClosed_le continuous_const (hc i)
    · exact isClosed_le (hc i) continuous_const

lemma sphereLabel_mem_region {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m))
    (i : Fin m) (b : Bool) (hy : sphereLabel y = (i.val,b)) : y ∈ labelRegion i b := by
  have hi : peakIndex y = i := Fin.ext (congrArg Prod.fst hy)
  have hb : decide (y (peakIndex y) < 0) = b := congrArg Prod.snd hy
  refine ⟨?_,?_⟩
  · intro j
    rw [← hi]
    exact maxIndex_le (fun j => |y j|) j
  · rw [← hb, hi]
    by_cases h : y i < 0
    · simp only [h, decide_true, ↓reduceIte]
      exact h.le
    · simp only [h, decide_false]
      exact le_of_not_gt h

lemma compact_label_locality {X : Type*} [MetricSpace X] [CompactSpace X]
    {m : ℕ} [NeZero m] (b : Fin m → Bool)
    (f g : X → EuclideanSpace ℝ (Fin m)) (hf : Continuous f) (hg : Continuous g)
    (U : Set X) (hU : IsOpen U)
    (heq : ∀ x ∈ U, f x = g x)
    (hfull : ∀ x, (∀ i, f x ∈ labelRegion i (b i)) ∨
      (∀ i, g x ∈ labelRegion i (b i)) → x ∈ U) :
    ∃ δ > 0, ∀ x : X,
      (∀ y, dist y x < δ → f y = g y) ∨
      ∃ i j : Fin m,
        (∀ y, dist y x < δ → sphereLabel (f y) ≠ (i.val,b i)) ∧
        (∀ y, dist y x < δ → sphereLabel (g y) ≠ (j.val,b j)) := by
  let c : Option (Fin m × Fin m) → Set X := fun o => match o with
    | none => U
    | some (i,j) => (f ⁻¹' labelRegion i (b i))ᶜ ∩ (g ⁻¹' labelRegion j (b j))ᶜ
  have hc : ∀ i, IsOpen (c i) := by
    intro o
    cases o with
    | none => exact hU
    | some p =>
      exact ((labelRegion_closed p.1 (b p.1)).preimage hf).isOpen_compl.inter
        ((labelRegion_closed p.2 (b p.2)).preimage hg).isOpen_compl
  have hcover : (Set.univ : Set X) ⊆ ⋃ o, c o := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨none,hx⟩
    · have hnf : ¬ ∀ i, f x ∈ labelRegion i (b i) := fun hh => hx (hfull x (Or.inl hh))
      have hng : ¬ ∀ i, g x ∈ labelRegion i (b i) := fun hh => hx (hfull x (Or.inr hh))
      obtain ⟨i,hi⟩ := not_forall.mp hnf
      obtain ⟨j,hj⟩ := not_forall.mp hng
      exact Set.mem_iUnion.mpr ⟨some (i,j),hi,hj⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcover
  refine ⟨δ,hδ,?_⟩
  intro x
  obtain ⟨o,ho⟩ := hball x (Set.mem_univ _)
  cases o with
  | none => exact Or.inl (fun y hy => heq y (ho hy))
  | some p =>
    refine Or.inr ⟨p.1,p.2,?_,?_⟩
    · intro y hy he
      exact (ho hy).1 (sphereLabel_mem_region _ _ _ he)
    · intro y hy he
      exact (ho hy).2 (sphereLabel_mem_region _ _ _ he)

lemma mapSimplex_coeff_zero_of_ne {V W : Type*} [DecidableEq V] [DecidableEq W]
    (L : PreAbstractSimplicialComplex W) (f : V → W) (s : Finset V)
    (t : {s : Finset W // s ∈ L}) (hne : s.image f ≠ t.val) :
    mapSimplex L f s t = 0 := by
  rw [mapSimplex]
  split_ifs <;> simp_all [simplex_coeff]

lemma image_ne_crossFacet_of_missing {V : Type*} [DecidableEq V] {m : ℕ}
    (s : Finset V) (f : V → SignedVertex) (b : Fin m → Bool)
    (i : Fin m) (hi : ∀ x ∈ s, f x ≠ (i.val,b i)) : s.image f ≠ crossFacet m b := by
  intro h
  have hm : (i.val,b i) ∈ s.image f := by
    rw [h]
    exact (mem_crossFacet m b _).mpr ⟨i,rfl⟩
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hm
  exact hi x hx he

lemma localized_approximation_coeff (n m : ℕ) (hn : 0 < n) [NeZero m]
    (b : Fin m → Bool)
    (f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f (annulus n)) (hg : ContinuousOn g (annulus n))
    (U : Set (annulus n)) (hU : IsOpen U)
    (heq : ∀ x : annulus n, x ∈ U → f x.val = g x.val)
    (hfull : ∀ x : annulus n, (∀ i, f x.val ∈ labelRegion i (b i)) ∨
      (∀ i, g x.val ∈ labelRegion i (b i)) → x ∈ U) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ =
      approximation n m r (fun x => sphereLabel (g x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ := by
  classical
  let : CompactSpace (annulus n) := isCompact_iff_compactSpace.mp (annulus_compact n)
  obtain ⟨δ,hδ,hlocal⟩ := compact_label_locality b (fun x : annulus n => f x.val)
    (fun x : annulus n => g x.val) hf.domRestrict hg.domRestrict U hU heq hfull
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let K := hemisphereComplex (n:ℝ) (E := EuclideanSpace ℝ (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} :=
    ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (f x)))
  let R : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (g x)))
  change T (fineCrossMap n r (crossFundamental n)) = R (fineCrossMap n r (crossFundamental n))
  apply linearMap_eq_of_support T R _
  intro s hs
  change mapChains K (cross m) (fun x => sphereLabel (f x)) (simplex K s.val) t =
    mapChains K (cross m) (fun x => sphereLabel (g x)) (simplex K s.val) t
  rw [mapChains_simplex K (cross m) _ s.property,mapChains_simplex K (cross m) _ s.property]
  have ha : ∀ x ∈ s.val, x ∈ annulus n := fun x hx => hemisphere_vertex_annulus n hn s.property hx
  obtain ⟨x,hx⟩ := s.property.1
  have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
  rcases hlocal ⟨x,ha x hx⟩ with he | ⟨i,j,hi,hj⟩
  · have himg : s.val.image (fun y => sphereLabel (f y)) = s.val.image (fun y => sphereLabel (g y)) := by
      apply Finset.image_congr
      intro y hy
      exact congrArg sphereLabel (he ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr))
    simp only [mapSimplex,himg]
  · rw [mapSimplex_coeff_zero_of_ne (cross m) _ s.val t, mapSimplex_coeff_zero_of_ne (cross m) _ s.val t]
    · apply image_ne_crossFacet_of_missing s.val _ b j
      intro y hy
      exact hj ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr)
    · apply image_ne_crossFacet_of_missing s.val _ b i
      intro y hy
      exact hi ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr)

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SignVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma signVector_norm (m : ℕ) (b : Fin m → Bool) : ‖signVector m b‖ = Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  have h (i : Fin m) : ‖signVector m b i‖ ^ 2 = (1:ℝ) := by
    simp only [signVector_apply]
    cases b i <;> norm_num
  simp only [h, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one]

lemma facetCenter_norm (m : ℕ) [NeZero m] (b : Fin m → Bool) : ‖facetCenter m b‖ = 1 := by
  rw [facetCenter, norm_smul, signVector_norm, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos_of_pos (by exact_mod_cast NeZero.pos m)))

lemma facetCenter_region (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    facetCenter m b ∈ labelRegion i (b i) := by
  have ha (j : Fin m) : |facetCenter m b j| = (Real.sqrt m)⁻¹ := by
    simp only [facetCenter, PiLp.smul_apply, smul_eq_mul, signVector_apply, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    cases b j <;> norm_num
  refine ⟨fun j => by rw [ha j,ha i],?_⟩
  change (if b i then (Real.sqrt m)⁻¹ * (if b i then (-1:ℝ) else 1) ≤ 0
    else 0 ≤ (Real.sqrt m)⁻¹ * (if b i then (-1:ℝ) else 1))
  have h := inv_nonneg.mpr (Real.sqrt_nonneg (m:ℝ))
  cases b i <;> simp_all

lemma all_labelRegions_iff_center (m : ℕ) [NeZero m] (b : Fin m → Bool)
    (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    (∀ i, y ∈ labelRegion i (b i)) ↔ y = facetCenter m b := by
  refine ⟨?_,fun he i => he ▸ facetCenter_region m b i⟩
  intro hyc
  let i₀ : Fin m := ⟨0,NeZero.pos m⟩
  let d : ℝ := |y i₀|
  have hd : 0 ≤ d := abs_nonneg _
  have hcoord (i : Fin m) : |y i| = d :=
    le_antisymm ((hyc i₀).1 i) ((hyc i).1 i₀)
  have hv : y = d • signVector m b := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, signVector_apply]
    have hsign := (hyc i).2
    change (if b i then y i ≤ 0 else 0 ≤ y i) at hsign
    cases hb : b i
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      simpa only [abs_of_nonneg hsign, mul_one] using hcoord i
    · simp only [hb, ↓reduceIte] at hsign ⊢
      have he := hcoord i
      rw [abs_of_nonpos hsign] at he
      linarith
  have hdval : d = (Real.sqrt m)⁻¹ := by
    have he := hy
    rw [hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,signVector_norm] at he
    exact eq_inv_of_mul_eq_one_left he
  rw [hv,hdval]
  rfl

lemma constant_approximation_facet_zero (n m r : ℕ) (hm : 1 < m) [NeZero m]
    (b : Fin m → Bool) (y : EuclideanSpace ℝ (Fin m)) :
    approximation n m r (fun _ => sphereLabel y) (crossFundamental n)
      ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ = 0 := by
  classical
  let K := hemisphereComplex (n:ℝ) (E := EuclideanSpace ℝ (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} := ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun _ => sphereLabel y))
  change T (fineCrossMap n r (crossFundamental n)) = 0
  have ht : T = 0 := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : T (simplex K s.val) = 0 := by
      change mapChains K (cross m) (fun _ => sphereLabel y) (simplex K s.val) t = 0
      rw [mapChains_simplex K (cross m) _ s.property]
      apply mapSimplex_coeff_zero_of_ne
      intro he
      have hc : (s.val.image (fun _ => sphereLabel y)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha c hc
        obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp hc
        rfl
      rw [he,crossFacet_card] at hc
      omega
    rw [simplex_of_mem K s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [ha,map_smul,hh,smul_zero,LinearMap.zero_apply]
  rw [ht,LinearMap.zero_apply]

lemma continuous_missed_facet_zero (n m : ℕ) (hn : 0 < n) (hm : 1 < m) [NeZero m]
    (b : Fin m → Bool) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f (annulus n)) (hfn : ∀ x ∈ annulus n, ‖f x‖ = 1)
    (hmiss : ∀ x ∈ annulus n, f x ≠ facetCenter m b) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ = 0 := by
  have hfneg : -(facetCenter m b) ≠ facetCenter m b := by
    intro he
    have hz : facetCenter m b = 0 := by
      ext i
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin m) => z i) he
      simp only [PiLp.neg_apply] at hi
      change facetCenter m b i = 0
      linarith
    have hn := facetCenter_norm m b
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨δ,hδ,hh⟩ := localized_approximation_coeff n m hn b f (fun _ => -(facetCenter m b))
    hf continuousOn_const ∅ isOpen_empty (by simp) (by
      intro x hx
      rcases hx with h | h
      · exact False.elim (hmiss x.val x.property ((all_labelRegions_iff_center m b _ (hfn _ x.property)).mp h))
      · exact False.elim (hfneg ((all_labelRegions_iff_center m b _ (by simp [facetCenter_norm])).mp h)))
  refine ⟨δ,hδ,fun r hr => ?_⟩
  rw [hh r hr,constant_approximation_facet_zero n m r hm b]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_OddHomotopySurjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open scoped RealInnerProductSpace

lemma odd_homotopy_surjective (n : ℕ) (hn : 1 < n) [NeZero n]
    (H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x))
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ = 1) :
    ∃ x ∈ annulus n, unitRadial (H (1,x)) = y := by
  classical
  by_contra hmiss
  push Not at hmiss
  let b : Fin n → Bool := fun _ => false
  let L := householder y (facetCenter n b)
  have hLy : L y = facetCenter n b := householder_send (hy.trans (facetCenter_norm n b).symm)
  let K : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun p => L (H p)
  have hK : ContinuousOn K (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := L.continuous.comp_continuousOn hH
  have hKz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, K p ≠ 0 := by
    intro p hp hz
    exact hHz p hp (L.injective (hz.trans (map_zero L).symm))
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => unitRadial (K (0,x))
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => unitRadial (K (1,x))
  have hU : ContinuousOn (fun p => unitRadial (K p)) (Set.Icc (0:ℝ) 1 ×ˢ annulus n) :=
    (unitRadial_continuousOn (S := {z | z ≠ 0}) (fun _ h => h)).comp hK hKz
  have hf : ContinuousOn f (annulus n) := hU.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  have hg : ContinuousOn g (annulus n) := hU.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn : ∀ x ∈ annulus n, ‖f x‖ = 1 := fun x hx =>
    unitRadial_norm (hKz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  have hgn : ∀ x ∈ annulus n, ‖g x‖ = 1 := fun x hx =>
    unitRadial_norm (hKz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfo : ∀ x ∈ annulus n, f (-x) = -f x := by
    intro x hx
    simp only [f,K,hHo x hx,map_neg,unitRadial_neg]
  have hgm : ∀ x ∈ annulus n, g x ≠ facetCenter n b := by
    intro x hx he
    have hnorm : L (unitRadial (H (1,x))) = unitRadial (K (1,x)) := by
      simp [unitRadial,K]
    apply hmiss x hx
    exact L.injective (hnorm.trans (he.trans hLy.symm))
  obtain ⟨δ₀,hδ₀,hdeg⟩ := eventually_odd_sphere_degree n hn f hf hfn hfo
  obtain ⟨δ₁,hδ₁,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl K hK hKz
  obtain ⟨δ₂,hδ₂,hzero⟩ := continuous_missed_facet_zero n n (by omega) hn b g hg hgn hgm
  have hnp : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have hq : ((n:ℝ)-1)/n < 1 := by apply (div_lt_one hnp).mpr; linarith
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < min δ₀ (min δ₁ δ₂) / 2 by positivity) hq
  have hr0 : (((n:ℝ)-1)/n)^r * 2 < δ₀ := by
    have hh := min_le_left δ₀ (min δ₁ δ₂); linarith
  have hr1 : (((n:ℝ)-1)/n)^r * 2 < δ₁ := by
    have hh := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_left δ₁ δ₂); linarith
  have hr2 : (((n:ℝ)-1)/n)^r * 2 < δ₂ := by
    have hh := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_right δ₁ δ₂); linarith
  have he := hhom r hr1
  change approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n) =
    approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) at he
  rw [hdeg r hr0] at he
  have hc := congrArg (fun c : Chain (cross n) => c ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩) he
  rw [crossFundamental_coeff n hn b,hzero r hr2] at hc
  exact one_ne_zero hc

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_TraceSphere
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section TraceSphere
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "M" => Matrix ν ν ℝ

omit [DecidableEq ν] in
lemma matrix_trace_continuous : Continuous (Matrix.trace : M → ℝ) :=
  (Matrix.traceLinearMap ν ℝ ℝ).continuous_of_finiteDimensional

omit [DecidableEq ν] in
lemma matrix_trace_nonneg {A : M} (hA : 0 ≤ A) : 0 ≤ Matrix.trace A :=
  (Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg

lemma traceAbs_pos {A : M} (hA : A ≠ 0) : 0 < Matrix.trace (CFC.abs A) := by
  have hp := matrix_trace_nonneg (CFC.abs_nonneg A)
  apply lt_of_le_of_ne hp
  intro hz
  have habs := (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)).trace_eq_zero_iff.mp hz.symm
  have he := CFC.abs_mul_abs A
  rw [habs,zero_mul] at he
  exact hA (Matrix.conjTranspose_mul_self_eq_zero.mp he.symm)

lemma traceRadial_mem {A : M} (hA : IsSelfAdjoint A) (hAz : A ≠ 0) :
    traceRadial A ∈ traceSphere ν := by
  have hp := traceAbs_pos hAz
  refine ⟨(IsSelfAdjoint.all (_ : ℝ)).smul hA,?_⟩
  change Matrix.trace (CFC.abs ((Matrix.trace (CFC.abs A))⁻¹ • A)) = 1
  rw [CFC.abs_smul,Matrix.trace_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ (ne_of_gt hp)

lemma traceRadial_continuousOn : ContinuousOn (traceRadial (ν := ν)) {A | A ≠ 0} :=
  ((matrix_trace_continuous.comp CFC.continuous_abs).continuousOn.inv₀
    (fun _A hA => ne_of_gt (traceAbs_pos hA))).smul continuous_id.continuousOn

lemma traceRadial_neg (A : M) : traceRadial (-A) = -traceRadial A := by
  simp only [traceRadial,CFC.abs_neg,smul_neg]

end TraceSphere
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_TraceHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator
open SimplicialChains
section TraceHomotopy
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι

omit [Nonempty ν] in
lemma Admissible.traceHomotopy_ray_oai {f : EuclideanSpace ℝ ν → ι → ℝ} (_hf : Admissible f)
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (G : ℝ × traceSphere ν → Y)
    (hG : ContinuousOn G (Set.Icc (0:ℝ) 1 ×ˢ Set.univ))
    (hG0 : ∀ A : traceSphere ν, G (0,A) = WithLp.toLp 2 (signedExtension f A.val))
    (hGz : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ A : traceSphere ν, G (t,A) ≠ 0)
    {y : Y} (hy : y ≠ 0) :
    ∃ A : traceSphere ν, ∃ t : ℝ, 0 < t ∧ G (1,A) = t • y := by
  classical
  let n := Fintype.card ι
  have hnz : n ≠ 0 := by dsimp [n]; omega
  let : NeZero n := ⟨hnz⟩
  let ea : UpperTriangle ν ≃ Fin n := (Fintype.equivFin _).trans (finCongr hc)
  let eaL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let ebL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let A : EuclideanSpace ℝ (Fin n) → M := fun x => symmetricCoordinates (eaL.symm x)
  have hAc : Continuous A := symmetricCoordinates.continuous_of_finiteDimensional.comp eaL.symm.continuous
  have hAs (x : EuclideanSpace ℝ (Fin n)) : IsSelfAdjoint (A x) := symmetricCoordinates_selfAdjoint _
  have hAz (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ annulus n) : A x ≠ 0 := by
    intro hz
    have h0 : eaL.symm x = 0 := symmetricCoordinates_injective (hz.trans (map_zero _).symm)
    have hx0 : x = 0 := eaL.symm.injective (h0.trans (map_zero _).symm)
    have hd := hx.1
    rw [hx0,norm_zero] at hd
    norm_num at hd
    exact hnz hd
  let N : annulus n → traceSphere ν := fun x =>
    ⟨traceRadial (A x.val),traceRadial_mem (hAs _) (hAz _ x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact traceRadial_continuousOn.comp_continuous (hAc.comp continuous_subtype_val)
      (fun x => hAz _ x.property)
  let H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun p =>
    if hx : p.2 ∈ annulus n then ebL (G (p.1,N ⟨p.2,hx⟩)) else 0
  have hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let S := Set.Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : S => N ⟨p.val.2,p.property.2⟩) :=
      hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hG.comp_continuous (continuous_subtype_val.fst.prodMk hcN)
      (fun p : S => ⟨p.property.1,Set.mem_univ _⟩)
    apply (ebL.continuous.comp hg).congr
    intro p
    change ebL (G (p.val.1,N ⟨p.val.2,p.property.2⟩)) = H p.val
    simp only [H,dite_eq_left p.property.2]
  have hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0 := by
    intro p hp hz
    have he : G (p.1,N ⟨p.2,hp.2⟩) = 0 := ebL.injective (by simpa only [H,dite_eq_left hp.2,map_zero] using hz)
    exact hGz _ hp.1 _ he
  have hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x) := by
    intro x hx
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [H,dite_eq_left hx,dite_eq_left hxn,hG0,N]
    have hAn : A (-x) = -A x := by simp only [A,map_neg]
    rw [hAn,traceRadial_neg,signedExtension_odd,WithLp.toLp_neg,map_neg]
  have hY : ‖ebL (unitRadial y)‖ = 1 := by rw [ebL.norm_map,unitRadial_norm hy]
  obtain ⟨x,hx,he⟩ := odd_homotopy_surjective n hn H hH hHz hHo hY
  let z : Y := G (1,N ⟨x,hx⟩)
  have hz : z ≠ 0 := hGz _ ⟨zero_le_one,le_rfl⟩ _
  have he' : unitRadial z = unitRadial y := by
    apply ebL.injective
    have heL : ebL (unitRadial z) = unitRadial (ebL z) := by simp only [unitRadial,map_smul,ebL.norm_map]
    rw [heL]
    simpa only [H,dite_eq_left hx] using he
  refine ⟨N ⟨x,hx⟩,‖z‖ / ‖y‖,div_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hy),?_⟩
  have hh := congrArg (fun v : Y => ‖z‖ • v) he'
  simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul,
    ← div_eq_mul_inv] using hh

end TraceHomotopy
end BorsukNine

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.BorsukNine.Admissible.traceHomotopy_ray_oai.{u_1, u_2} := @OAI.BorsukNine.Admissible.traceHomotopy_ray_oai.{u_1, u_2}
