-- Prove2me | solution 1 for OAI.EilenbergGanea.source_no_classifyingSpace_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T06:55:18.842991+00:00
-- url     : https://prove2.me/submissions/426a0e70-011b-474d-9d9f-6329dcc61bde

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIStdSimplexCompat
import Definitions.Def_OAIEGC004
import Theorems.Thm_OAI_EilenbergGanea_boundary_basis_small_transport
import Theorems.Thm_OAI_EilenbergGanea_source_residuallyFinite

section
-- module Solutions.OAIEG.RightAngledArtin_Basic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea


section FiniteGeneration
variable {V : Type*} (L : SimpleGraph V)

theorem edge_difference_mem {v w : V} (h : L.Adj v w) :
    artinGenerator L v * (artinGenerator L w)⁻¹ ∈ edgeGenerated L :=
  Subgroup.subset_closure ⟨v, w, h, rfl⟩

theorem reachable_difference_mem {v w : V} (h : L.Reachable v w) :
    artinGenerator L v * (artinGenerator L w)⁻¹ ∈ edgeGenerated L := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    simpa only [mul_assoc, inv_mul_cancel_left] using
      (edgeGenerated L).mul_mem (edge_difference_mem L huv) ih

theorem reachable_inv_difference_mem {v w : V} (h : L.Reachable v w) :
    (artinGenerator L v)⁻¹ * artinGenerator L w ∈ edgeGenerated L := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have hc := (adjacent_generators_commute L huv).inv_left
    have he : (artinGenerator L u)⁻¹ * artinGenerator L v ∈ edgeGenerated L := by
      rw [hc.eq]
      exact edge_difference_mem L huv.symm
    simpa only [mul_assoc, mul_inv_cancel_left] using (edgeGenerated L).mul_mem he ih


/-- A group-theoretic conjugation identity used with edge differences. -/
theorem conjugate_mem_of_difference {A : Type*} [Group A] (K : Subgroup A)
    {g a e : A} (hga : g * a⁻¹ ∈ K) (he : e ∈ K) (ha : Commute a e) :
    g * e * g⁻¹ ∈ K := by
  have hm := K.mul_mem (K.mul_mem hga he) (K.inv_mem hga)
  have hi : (g * a⁻¹) * e * (g * a⁻¹)⁻¹ = g * e * g⁻¹ := by
    calc
      (g * a⁻¹) * e * (g * a⁻¹)⁻¹ = g * (a⁻¹ * e * a) * g⁻¹ := by group
      _ = g * e * g⁻¹ := by rw [ha.inv_left.eq]; simp [mul_assoc]
  rwa [hi] at hm

theorem generator_conjugate_mem (hconn : L.Preconnected) (v : V)
    {x : ArtinGroup L} (hx : x ∈ edgeGenerated L) :
    artinGenerator L v * x * (artinGenerator L v)⁻¹ ∈ edgeGenerated L := by
  have hh : edgeGenerated L ≤ (edgeGenerated L).comap (MulAut.conj (artinGenerator L v)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨b, c, hbc, rfl⟩
    exact conjugate_mem_of_difference (edgeGenerated L)
      (reachable_difference_mem L (hconn v b)) (edge_difference_mem L hbc)
      ((Commute.refl _).mul_right (adjacent_generators_commute L hbc).inv_right)
  exact hh hx

theorem generator_inv_conjugate_mem (hconn : L.Preconnected) (v : V)
    {x : ArtinGroup L} (hx : x ∈ edgeGenerated L) :
    (artinGenerator L v)⁻¹ * x * artinGenerator L v ∈ edgeGenerated L := by
  have hh : edgeGenerated L ≤
      (edgeGenerated L).comap (MulAut.conj ((artinGenerator L v)⁻¹)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨b, c, hbc, rfl⟩
    change (artinGenerator L v)⁻¹ * (artinGenerator L b * (artinGenerator L c)⁻¹) *
      ((artinGenerator L v)⁻¹)⁻¹ ∈ edgeGenerated L
    apply conjugate_mem_of_difference (edgeGenerated L) (a := (artinGenerator L b)⁻¹)
    · simpa using reachable_inv_difference_mem L (hconn v b)
    · exact edge_difference_mem L hbc
    · exact ((Commute.refl _).mul_right
        (adjacent_generators_commute L hbc).inv_right).inv_left
  simpa using hh hx

theorem edgeGenerated_normal (hconn : L.Preconnected) : (edgeGenerated L).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply (Subgroup.eq_top_iff' _).mpr
  apply PresentedGroup.generated_by
  intro v
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact generator_conjugate_mem L hconn v
  · intro hx
    simpa [mul_assoc] using generator_inv_conjugate_mem L hconn v hx

/-- For a connected defining graph, edge differences generate the full height kernel. -/
theorem edgeGenerated_eq_height_kernel (hconn : L.Preconnected) (v₀ : V) :
    edgeGenerated L = (height L).ker := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨v, w, _, rfl⟩
    simp [MonoidHom.mem_ker]
  · let _ := edgeGenerated_normal L hconn
    let q := QuotientGroup.mk' (edgeGenerated L)
    let z := zpowersHom _ (q (artinGenerator L v₀))
    have hq : q = z.comp (height L) := by
      apply PresentedGroup.ext
      intro v
      change q (artinGenerator L v) = z (height L (artinGenerator L v))
      rw [height_generator]
      change q (artinGenerator L v) = q (artinGenerator L v₀) ^ (1 : ℤ)
      rw [zpow_one]
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (reachable_difference_mem L (hconn v v₀))
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change q x = 1
    rw [hq, MonoidHom.comp_apply, (MonoidHom.mem_ker.mp hx), map_one]

end FiniteGeneration

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_TraceWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
/-! Signed trace normal forms and slowly varying barycentric directions. -/

namespace TraceWords

variable {V : Type*} (L : SimpleGraph V)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)


/-! The occurrence-level normal form is now used to control an actual generator
step. No geometric normal-form or direction-vector assertion is assumed. -/

variable {L}


section RootCounts
variable [LinearOrder V]
variable (L)

theorem rootScan_append (s : Multiset (V × V)) (w v : Word V) :
    rootScan L s (w ++ v) = rootScan L (rootScan L s w) v := List.foldl_append

variable {L}

variable (L)

theorem wordCounts_append_singleton (w : Word V) (x : Letter V) :
    wordCounts L (w ++ [x]) = wordCounts L w +
      Finsupp.single (nextRoot L (rootScan L 0 w) x.1) 1 := by
  simp only [wordCounts,rootScan_append,rootScan_cons,rootScan_nil,rootInsert,rootCounts_cons]
  exact add_comm _ _


theorem traceCounts_append_singleton (t : Trace L) (x : Letter V) :
    ∃ r, traceCounts L (appendTrace L t (ofWord L [x])) = traceCounts L t + Finsupp.single r 1 := by
  induction t using Quotient.inductionOn with
  | h w => exact ⟨_,wordCounts_append_singleton L w x⟩

omit [LinearOrder V] in
 theorem support_subset_singleton_add (c : V →₀ ℕ) (r : V) :
    c.support ⊆ (c + Finsupp.single r 1).support := by
  intro v hv
  apply Finsupp.mem_support_iff.mpr
  intro h
  apply Finsupp.mem_support_iff.mp hv
  exact (Nat.add_eq_zero_iff.mp (show c v + (Finsupp.single r 1) v = 0 from h)).1

theorem traceCounts_append_support (t : Trace L) (x : Letter V) :
    (traceCounts L t).support ⊆ (traceCounts L (appendTrace L t (ofWord L [x]))).support := by
  obtain ⟨r,hr⟩ := traceCounts_append_singleton L t x
  rw [hr]
  exact support_subset_singleton_add _ _

end RootCounts

variable (L)


section DirectionVectors
variable [Fintype V] [LinearOrder V]

/-- The exact finite-coordinate estimate used in the manuscript's direction map. -/
theorem count_normalization_bound (c : V →₀ ℕ) (r : V) {n : ℕ}
    (hn : 0 < n) (hs : ∑ v, c v = n) :
    ∑ v, |((c + Finsupp.single r 1 : V →₀ ℕ) v : ℝ) / (n + 1 : ℝ) -
      (c v : ℝ) / (n : ℝ)| ≤ 2 / (n + 1 : ℝ) := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hd : 0 < (n + 1 : ℝ) := by positivity
  have hi (v : V) :
      ((c + Finsupp.single r 1 : V →₀ ℕ) v : ℝ) / (n + 1 : ℝ) - (c v : ℝ) / (n : ℝ) =
      (((Finsupp.single r (1 : ℕ)) v : ℝ) - (c v : ℝ) / n) / (n + 1 : ℝ) := by
    simp only [Finsupp.add_apply,Nat.cast_add]
    field_simp [hn0,ne_of_gt hd]
    ring
  have hpoint (v : V) :
      |((c + Finsupp.single r 1 : V →₀ ℕ) v : ℝ) / (n + 1 : ℝ) - (c v : ℝ) / (n : ℝ)| ≤
      (((Finsupp.single r (1 : ℕ)) v : ℝ) + (c v : ℝ) / n) / (n + 1 : ℝ) := by
    rw [hi,abs_div,abs_of_pos hd]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ ≤ |(((Finsupp.single r (1 : ℕ)) v : ℝ))| + |(c v : ℝ) / n| :=
        abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  calc
    _ ≤ ∑ v, (((Finsupp.single r (1 : ℕ)) v : ℝ) + (c v : ℝ) / n) /
        (n + 1 : ℝ) := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = 2 / (n + 1 : ℝ) := by
      rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.sum_div]
      simp only [← Nat.cast_sum,hs]
      norm_num [Finsupp.single_apply,div_self hn0]

theorem traceDirection_append_bound (t : Trace L) (x : Letter V)
    (ht : 0 < traceLength L t) :
    ∑ v, |traceDirection L (appendTrace L t (ofWord L [x])) v - traceDirection L t v| ≤
      2 / (traceLength L t + 1 : ℝ) := by
  obtain ⟨r,hr⟩ := traceCounts_append_singleton L t x
  simp only [traceDirection,traceLength_append_singleton,hr,Nat.cast_add,Nat.cast_one]
  exact count_normalization_bound (traceCounts L t) r ht (traceCounts_sum L t)

omit [Fintype V] in
theorem traceCounts_step_common_simplex (t : Trace L) (x : Letter V) :
    (((traceCounts L t).support ∪
      (traceCounts L (appendTrace L t (ofWord L [x]))).support : Finset V) : Set V).Pairwise L.Adj := by
  rw [Finset.union_eq_right.mpr (traceCounts_append_support L t x)]
  exact traceCounts_support_clique L _

/-- Full trace-direction step, for the actual generators of the Artin presentation.
The shorter normal trace controls both the common simplex and the uniform l1 bound. -/
theorem artinDirection_right_step (g : ArtinGroup L) (x : Letter V)
    (hg : 0 < traceLength L (artinNormalTrace L g))
    (hgx : 0 < traceLength L (artinNormalTrace L
      (g * letterValue (artinGenerator L) x))) :
    let t := artinNormalTrace L g
    let t' := artinNormalTrace L (g * letterValue (artinGenerator L) x)
    (((traceCounts L t).support ∪ (traceCounts L t').support : Finset V) : Set V).Pairwise L.Adj ∧
    ∃ n : ℕ, 0 < n ∧
      ((traceLength L t = n ∧ traceLength L t' = n + 1) ∨
        (traceLength L t' = n ∧ traceLength L t = n + 1)) ∧
      ∑ v, |artinDirection L (g * letterValue (artinGenerator L) x) v -
        artinDirection L g v| ≤ 2 / (n + 1 : ℝ) := by
  dsimp only
  rcases artinNormalTrace_right_step L g x with h | h
  · rw [h] at hgx ⊢
    refine ⟨traceCounts_step_common_simplex L _ x,
      traceLength L (artinNormalTrace L g),hg,Or.inl ⟨rfl,?_⟩,?_⟩
    · exact traceLength_append_singleton L _ x
    · simpa only [artinDirection,h] using
        traceDirection_append_bound L (artinNormalTrace L g) x hg
  · rw [h] at hg ⊢
    refine ⟨?_,traceLength L (artinNormalTrace L
      (g * letterValue (artinGenerator L) x)),hgx,Or.inr ⟨rfl,?_⟩,?_⟩
    · rw [Finset.union_comm]
      exact traceCounts_step_common_simplex L _ _
    · exact traceLength_append_singleton L _ _
    · simpa only [artinDirection,h,abs_sub_comm] using
        traceDirection_append_bound L
          (artinNormalTrace L (g * letterValue (artinGenerator L) x)) (invLetter x) hgx

end DirectionVectors


section CommutingPowerDirections
variable {L}

theorem Extract.mem {x : Letter V} {w v : Word V} (h : Extract L x w v) : x ∈ w := by
  induction h with
  | head => simp
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

theorem same_sign_reduced {w : Word V} (b : Bool) (hw : ∀ x ∈ w, x.2 = b) :
    Reduced L (ofWord L w) := by
  intro t ht
  obtain ⟨v,hv,_⟩ := ht.representative
  suffices ∀ {w v : Word V}, Step L w v → (∀ x ∈ w, x.2 = b) → False from this hv hw
  intro w v h
  induction h with
  | @head x w v he =>
      intro hh
      have hx := hh x (by simp)
      have hi := hh (invLetter x) (List.mem_cons_of_mem _ he.mem)
      simp only [invLetter,hx] at hi
      cases b <;> cases hi
  | cons x h ih =>
      intro hh
      exact ih (fun _ h => hh _ (List.mem_cons_of_mem _ h))

variable (L)
variable [LinearOrder V]

theorem nextRoot_self {s : Multiset (V × V)} {v : V}
    (hs : ∀ p ∈ s, p.2 = p.1) (hv : ∀ p ∈ s, p.1 = v ∨ L.Adj p.1 v) :
    nextRoot L s v = v := by
  classical
  unfold nextRoot
  split_ifs with h
  · obtain ⟨p,hp,hdep,hroot⟩ := mem_predecessorRoots.mp (Finset.min'_mem _ h)
    rw [← hroot,hs p hp]
    exact (hv p hp).resolve_right hdep
  · rfl

theorem rootScan_clique {C : Set V} (hC : C.Pairwise L.Adj)
    {s : Multiset (V × V)} (hs : ∀ p ∈ s, p.1 ∈ C ∧ p.2 = p.1)
    {w : Word V} (hw : ∀ x ∈ w, x.1 ∈ C) :
    rootScan L s w = ((w.map (fun x => (x.1,x.1))) : Multiset (V × V)) + s := by
  classical
  induction w generalizing s with
  | nil => simp
  | cons x w ih =>
      have hx : x.1 ∈ C := hw x (by simp)
      have hr : nextRoot L s x.1 = x.1 := by
        apply nextRoot_self L (fun p hp => (hs p hp).2)
        intro p hp
        by_cases hpv : p.1 = x.1
        · exact Or.inl hpv
        · exact Or.inr (hC (hs p hp).1 hx hpv)
      have hi : ∀ p ∈ rootInsert L s x.1, p.1 ∈ C ∧ p.2 = p.1 := by
        intro p hp
        simp only [rootInsert,hr,Multiset.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨hx,rfl⟩
        · exact hs p hp
      rw [rootScan_cons,ih hi (fun y hy => hw y (List.mem_cons_of_mem _ hy))]
      simp [rootInsert,hr,← Multiset.cons_coe,Multiset.add_cons]

theorem wordCounts_clique {C : Set V} (hC : C.Pairwise L.Adj)
    {w : Word V} (hw : ∀ x ∈ w, x.1 ∈ C) :
    wordCounts L w = (w.map (fun x => Finsupp.single x.1 (1 : ℕ))).sum := by
  rw [wordCounts,rootScan_clique L hC (by simp) hw]
  simp only [add_zero,rootCounts,Multiset.map_coe,List.map_map,Multiset.sum_coe,Function.comp_def]

theorem counts_negative_commuting_powers {q r : V} (hqr : L.Adj q r) (n m : ℕ) :
    traceCounts L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m)) =
      Finsupp.single q n + Finsupp.single r m := by
  classical
  let w : Word V := List.replicate n (q,false) ++ List.replicate m (r,false)
  have hn : ∀ x ∈ w, x.2 = false := by
    intro x hx
    simp only [w,List.mem_append,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl
  have hC : ({q,r} : Set V).Pairwise L.Adj := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hqr
    · exact L.symm.symm _ _ hqr
    · exact False.elim (hab rfl)
  have hwc : ∀ x ∈ w, x.1 ∈ ({q,r} : Set V) := by
    intro x hx
    simp only [w,List.mem_append,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
  have he : wordEval (artinGenerator L) w =
      (artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m := by
    simp [wordEval,w,List.map_replicate]
  rw [← he,artinNormalTrace_word,(same_sign_reduced false hn).normalTrace_eq,
    traceCounts_ofWord,wordCounts_clique L hC hwc]
  ext v
  simp [w,List.map_replicate,Finsupp.single_apply]

end CommutingPowerDirections

section HeightAndExactDirections

variable [Fintype V] [LinearOrder V]

theorem length_negative_commuting_powers {q r : V} (hqr : L.Adj q r) (n m : ℕ) :
    traceLength L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m)) = n + m := by
  rw [← traceCounts_sum,counts_negative_commuting_powers L hqr]
  simp [Finsupp.single_apply,Finset.sum_add_distrib]

theorem direction_negative_commuting_powers {q r : V} (hqr : L.Adj q r)
    (n m : ℕ) (v : V) :
    artinDirection L ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m) v =
      ((if q = v then n else 0 : ℕ) + (if r = v then m else 0 : ℕ) : ℝ) / (n + m : ℝ) := by
  rw [artinDirection,traceDirection,counts_negative_commuting_powers L hqr,
    length_negative_commuting_powers L hqr]
  simp only [Finsupp.add_apply,Finsupp.single_apply,Nat.cast_add,Nat.cast_ite,Nat.cast_zero]

end HeightAndExactDirections

end TraceWords

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.UnitaryWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology
open scoped Quaternion ContDiff

open scoped Quaternion
namespace EilenbergGanea

open Set Filter Topology
open scoped ContDiff

theorem normalizeQuaternion_coe_of_ne_zero {q : ℍ} (hq : q ≠ 0) :
    (normalizeQuaternion q : ℍ) = ‖q‖⁻¹ • q := by simp [normalizeQuaternion, hq]

theorem normalizeQuaternion_coe_contDiffAt {q : ℍ} (hq : q ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => (normalizeQuaternion z : ℍ)) q := by
  have h : ContDiffAt ℝ ∞ (fun z : ℍ => ‖z‖⁻¹ • z) q :=
    ((contDiffAt_norm ℝ hq).inv (norm_ne_zero_iff.mpr hq)).smul contDiffAt_id
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hq] with z hz
  exact normalizeQuaternion_coe_of_ne_zero hz

theorem normalizeQuaternion_continuousAt {q : ℍ} (hq : q ≠ 0) :
    ContinuousAt normalizeQuaternion q := by
  exact tendsto_subtype_rng.mpr (normalizeQuaternion_coe_contDiffAt hq).continuousAt

@[simp] theorem normalizeQuaternion_unitary (q : SU2) : normalizeQuaternion (q : ℍ) = q := by
  have hqnorm : ‖(q : ℍ)‖ = 1 := (quaternion_mem_unitary_iff _).mp q.property
  have hq : (q : ℍ) ≠ 0 := by intro he; simp [he] at hqnorm
  apply Subtype.ext
  simp [normalizeQuaternion_coe_of_ne_zero hq, hqnorm]

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.SmallHolonomy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open scoped Quaternion ContDiff

@[simp] theorem smallQuaternionArc_zero (a : SU2) : smallQuaternionArc a 0 = 1 := by
  simpa [smallQuaternionArc, arcBlend] using (normalizeQuaternion_unitary (1 : SU2))

@[simp] theorem smallQuaternionArc_one (a : SU2) : smallQuaternionArc a 1 = a := by
  simp [smallQuaternionArc, arcBlend]

end EilenbergGanea

namespace EilenbergGanea

variable {Γ S H : Type*} [Group Γ] [Group H]

 theorem pathProduct_conjugate_loop (v : S → Γ) (a : Γ → S → H)
    (u r : FreeGroup S) (hr : wordValue v r = 1) (g : Γ) :
    pathProduct v a (u*r*u⁻¹) g = pathProduct v a u g *
      pathProduct v a r (g * wordValue v u) * (pathProduct v a u g)⁻¹ := by
  rw [pathProduct_mul, pathProduct_mul, pathProduct_inv, map_mul, hr, mul_one]
  simp only [mul_inv_cancel_right]

 theorem pathChain_conjugate (v : S → Γ) (u r : FreeGroup S)
    (hr : wordValue v r = 1) (g : Γ) :
    pathChain v (u*r*u⁻¹) g = pathChain v r (g * wordValue v u) := by
  simp only [pathChain, pathProduct_conjugate_loop v _ u r hr g,
    toAdd_mul, toAdd_inv]
  abel

end EilenbergGanea

open scoped Quaternion


end

end OAI
end

section
-- module Solutions.OAIEG.AffineTransport
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace AffineTransport

/-- A finite family of proper quaternion subspaces cannot cover ℍ. -/
theorem exists_avoid_subspaces {I : Type*} [Finite I]
    (p : I → Submodule ℝ ℍ) (hp : ∀ i, p i ≠ ⊤) :
    ∃ q : ℍ, ∀ i, q ∉ p i := by
  have ho (i) : IsOpen ((p i : Set ℍ)ᶜ) :=
    (p i).closed_of_finiteDimensional.isOpen_compl
  have hd (i) : Dense ((p i : Set ℍ)ᶜ) := by
    apply interior_eq_empty_iff_dense_compl.mp
    apply Set.not_nonempty_iff_eq_empty.mp
    intro h
    exact hp i ((p i).eq_top_of_nonempty_interior' h)
  obtain ⟨q,hq⟩ := (dense_iInter_of_isOpen ho hd).nonempty
  exact ⟨q,Set.mem_iInter.mp hq⟩

/-- Simultaneous general position for finitely many local quaternion gauges.
Different vertices may use different invertible linear transformations in each
chart. No flatness or topology is assumed in this finite-dimensional lemma. -/
theorem exists_triangle_general_position {A V : Type*} [Finite A] [Fintype V]
    (T : A → V → ℍ ≃ₗ[ℝ] ℍ) :
    ∃ q : V → ℍ, ∀ a (s : Finset V), s.card ≤ 3 →
      LinearIndepOn ℝ (fun v => T a v (q v)) (s : Set V) := by
  classical
  suffices ∀ U : Finset V, ∃ q : V → ℍ, ∀ a (s : Finset V), s ⊆ U → s.card ≤ 3 →
      LinearIndepOn ℝ (fun v => T a v (q v)) (s : Set V) by
    obtain ⟨q,hq⟩ := this Finset.univ
    exact ⟨q,fun a s h => hq a s (Finset.subset_univ _) h⟩
  intro U
  induction U using Finset.induction with
  | empty =>
      refine ⟨0,?_⟩
      intro a s hs _
      have : s = ∅ := Finset.subset_empty.mp hs
      subst s
      simpa only [Finset.coe_empty,Pi.zero_apply] using
        linearIndepOn_empty ℝ (fun v => T a v (0 : ℍ))
  | @insert v U hv ih =>
      obtain ⟨q,hq⟩ := ih
      let I := A × {s : Finset V // s ⊆ U ∧ s.card ≤ 2}
      let p : I → Submodule ℝ ℍ := fun i =>
        (Submodule.span ℝ ((fun w => T i.1 w (q w)) '' (i.2.val : Set V))).comap
          (T i.1 v).toLinearMap
      have hp (i : I) : p i ≠ ⊤ := by
        have hf : Module.finrank ℝ (Submodule.span ℝ
            ((fun w => T i.1 w (q w)) '' (i.2.val : Set V))) ≤ 2 := by
          have hh := finrank_span_finset_le_card (R := ℝ) (i.2.val.image (fun w => T i.1 w (q w)))
          rw [Finset.coe_image] at hh
          exact hh.trans ((Finset.card_image_le).trans i.2.property.2)
        have hproper : Submodule.span ℝ ((fun w => T i.1 w (q w)) ''
            (i.2.val : Set V)) ≠ ⊤ := by
          apply ne_of_lt (Submodule.lt_top_of_finrank_lt_finrank _)
          rw [Quaternion.finrank_eq_four]
          omega
        intro hh
        apply hproper
        apply top_unique
        intro x _
        have hm : (T i.1 v).symm x ∈ p i := by rw [hh]; trivial
        simpa only [p,Submodule.mem_comap,LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply] using hm
      obtain ⟨z,hz⟩ := exists_avoid_subspaces p hp
      refine ⟨Function.update q v z,?_⟩
      intro a s hs hc
      by_cases hvs : v ∈ s
      · have hsub : s.erase v ⊆ U := by
          intro w hw
          have hh := hs (Finset.mem_of_mem_erase hw)
          exact (Finset.mem_insert.mp hh).resolve_left (Finset.ne_of_mem_erase hw)
        have hcard : (s.erase v).card ≤ 2 := by
          have he := Finset.card_erase_add_one hvs
          omega
        have heq : ∀ w ∈ (s.erase v : Finset V), Function.update q v z w = q w := by
          intro w hw
          exact Function.update_of_ne (Finset.ne_of_mem_erase hw) _ _
        have hi : LinearIndepOn ℝ (fun w => T a w (Function.update q v z w))
            ((s.erase v : Finset V) : Set V) := by
          apply (hq a (s.erase v) hsub (by omega)).congr
          intro w hw
          dsimp only
          rw [heq w hw]
        have hn : T a v (Function.update q v z v) ∉ Submodule.span ℝ
            ((fun w => T a w (Function.update q v z w)) ''
              ((s.erase v : Finset V) : Set V)) := by
          rw [Function.update_self]
          have him : ((fun w => T a w (Function.update q v z w)) ''
              ((s.erase v : Finset V) : Set V)) =
              ((fun w => T a w (q w)) '' ((s.erase v : Finset V) : Set V)) := by
            apply Set.image_congr
            intro w hw
            rw [heq w hw]
          rw [him]
          exact hz ⟨a,⟨s.erase v,hsub,hcard⟩⟩
        have ht := (linearIndepOn_insert (by simp : v ∉ ((s.erase v : Finset V) : Set V))).mpr
          ⟨hi,hn⟩
        simpa only [← Finset.coe_insert,Finset.insert_erase hvs] using ht
      · have hsub : s ⊆ U := by
          intro w hw
          have hh := hs hw
          rcases Finset.mem_insert.mp hh with rfl | hh
          · exact False.elim (hvs hw)
          · exact hh
        apply (hq a s hsub hc).congr
        intro w hw
        dsimp only
        rw [Function.update_of_ne (by intro h; subst w; exact hvs hw)]


theorem normalize_left (h : SU2) {q : ℍ} (hq : q ≠ 0) :
    normalizeQuaternion ((h : ℍ) * q) = h * normalizeQuaternion q := by
  have hh : (h : ℍ) * q ≠ 0 := by
    exact (leftLinearEquiv h).map_ne_zero_iff.mpr hq
  apply Subtype.ext
  rw [normalizeQuaternion_coe_of_ne_zero hh]
  change ‖(h : ℍ) * q‖⁻¹ • ((h : ℍ) * q) = (h : ℍ) * (normalizeQuaternion q : ℍ)
  rw [normalizeQuaternion_coe_of_ne_zero hq,norm_mul,unit_norm,one_mul,mul_smul_comm]

section FiniteSimplex
variable {V : Type*} [Fintype V]

omit [Fintype V] in
private theorem isClosed_face_support (s : Finset V) :
    IsClosed {b : V → ℝ | ∀ v ∉ s, b v = 0} := by
  have he : {b : V → ℝ | ∀ v ∉ s, b v = 0} =
      ⋂ v, ⋂ (_ : v ∉ s), {b : V → ℝ | b v = 0} := by ext b; simp
  rw [he]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply v) continuous_const

theorem isCompact_face (s : Finset V) : IsCompact (face s) := by
  have compact_simplex : IsCompact (coordinateSimplex : Set (V → ℝ)) := by
    convert isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous using 1
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext weights
    simp [coordinateSimplex]
  exact compact_simplex.inter_right (isClosed_face_support s)

theorem isCompact_triangleSet : IsCompact (triangleSet : Set (V → ℝ)) :=
  isCompact_iUnion fun _ => isCompact_face _

instance instCompactSpaceElemForallRealTrianglePoint : CompactSpace (TrianglePoint V) :=
  isCompact_iff_compactSpace.mp isCompact_triangleSet

variable (h : V → V → SU2) (q : V → ℍ)

theorem exists_generalPosition : ∃ q : V → ℍ, GeneralPosition h q := by
  obtain ⟨q,hq⟩ := exists_triangle_general_position (fun a v => leftLinearEquiv (h a v))
  exact ⟨q,hq⟩

theorem rawGauge_ne_zero (hq : GeneralPosition h q) (a : V) (b : TrianglePoint V) :
    rawGauge h q a b ≠ 0 := by
  classical
  obtain ⟨s,hs,hb,hout⟩ := mem_triangleSet.mp b.property
  intro he
  have he' : ∑ v ∈ s, (b : V → ℝ) v • ((h a v : ℍ) * q v) = 0 := by
    rw [← he]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    rw [hout v hv,zero_smul]
  have hz := (linearIndepOn_iff'.mp (hq a s hs)) s b (Set.Subset.refl _) he'
  have hall : ∀ v, (b : V → ℝ) v = 0 := by
    intro v
    by_cases hv : v ∈ s
    · exact hz v hv
    · exact hout v hv
  have heq := hb.2
  simp only [hall,Finset.sum_const_zero] at heq
  norm_num at heq

theorem continuous_rawGauge (a : V) : Continuous (rawGauge h q a) :=
  continuous_finsetSum _ fun v _ => (continuous_apply v).smul continuous_const

theorem continuous_gauge (hq : GeneralPosition h q) (a : V) : Continuous (gauge h q a) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  exact ContinuousAt.comp (f := fun c : TrianglePoint V => rawGauge h q a c)
    (normalizeQuaternion_continuousAt (rawGauge_ne_zero h q hq a b))
    ((continuous_rawGauge h q a).comp continuous_subtype_val).continuousAt

/-- Uniform modulus over all charts, including across the edges of all simplices. -/
theorem gauges_uniform (hq : GeneralPosition h q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b c : TrianglePoint V, dist b c < δ →
      ∀ a, dist (gauge h q a b) (gauge h q a c) < ε := by
  have hc : Continuous (fun b : TrianglePoint V => fun a => gauge h q a b) :=
    continuous_pi fun a => continuous_gauge h q hq a
  have hu := CompactSpace.uniformContinuous_of_continuous hc
  obtain ⟨δ,hδ,H⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ,hδ,?_⟩
  intro b c hbc a
  exact lt_of_le_of_lt (dist_le_pi_dist (fun a => gauge h q a b) (fun a => gauge h q a c) a) (H hbc)

end FiniteSimplex

theorem unitary_dist_left (a b c : SU2) : dist (a * b) (a * c) = dist b c := by
  change dist ((a : ℍ) * (b : ℍ)) ((a : ℍ) * (c : ℍ)) = dist (b : ℍ) (c : ℍ)
  rw [dist_eq_norm,dist_eq_norm,← mul_sub,norm_mul,unit_norm,one_mul]

theorem unitary_dist_inv_mul_one (a b : SU2) : dist (a⁻¹ * b) 1 = dist a b := by
  rw [← unitary_dist_left a (a⁻¹ * b) 1]
  simp [dist_comm]

theorem unitary_dist_mul_one_le (a b : SU2) :
    dist (a * b) 1 ≤ dist a 1 + dist b 1 := by
  calc
    dist (a * b) 1 ≤ dist (a * b) a + dist a 1 := dist_triangle _ _ _
    _ = dist b 1 + dist a 1 := by
      exact congrArg (fun t => t + dist a 1) (by simpa only [mul_one] using unitary_dist_left a b 1)
    _ = dist a 1 + dist b 1 := add_comm _ _

section Connection
variable {V : Type*} [Fintype V]
variable (L : SimpleGraph V)

theorem root_mem (b : TrianglePoint V) : (b : V → ℝ) (root b) ≠ 0 :=
  Classical.choose_spec (point_exists_nonzero b)

variable (h : V → V → SU2) (q : V → ℍ)

theorem rawGauge_transition (hf : FlatConnection L h) {a c : V}
    {b : TrianglePoint V} (hac : Related L a c) (ha : Star L a b) (hc : Star L c b) :
    rawGauge h q a b = (h a c : ℍ) * rawGauge h q c b := by
  classical
  simp only [rawGauge,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : (b : V → ℝ) v = 0
  · simp [hv]
  · rw [mul_smul_comm,← mul_assoc,← Submonoid.coe_mul,hf a c v hac (hc v hv) (ha v hv)]

theorem gauge_transition (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {a c : V} {b : TrianglePoint V} (hac : Related L a c)
    (ha : Star L a b) (hc : Star L c b) :
    gauge h q a b = h a c * gauge h q c b := by
  unfold gauge
  rw [rawGauge_transition L h q hf hac ha hc]
  exact normalize_left _ (rawGauge_ne_zero h q hq c b)

theorem transport_chart (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {b c : TrianglePoint V} (hb : Compatible L b c) {a : V}
    (hab : Star L a b) (hac : Star L a c) :
    transport h q b c = chartTransport h q a b c := by
  have hrb : Star L (root b) b := fun v hv => hb _ _ (Or.inl (root_mem b)) (Or.inl hv)
  have hrc : Star L (root b) c := fun v hv => hb _ _ (Or.inl (root_mem b)) (Or.inr hv)
  have har : Related L a (root b) := hab _ (root_mem b)
  unfold transport chartTransport
  rw [gauge_transition L h q hf hq har hab hrb,
    gauge_transition L h q hf hq har hac hrc]
  group

theorem compatible_symm {b c : TrianglePoint V} (hb : Compatible L b c) :
    Compatible L c b := fun v w hv hw => hb v w hv.symm hw.symm

theorem transport_reverse (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {b c : TrianglePoint V} (hb : Compatible L b c) :
    transport h q c b = (transport h q b c)⁻¹ := by
  have hrc : Star L (root b) c := fun v hv => hb _ _ (Or.inl (root_mem b)) (Or.inr hv)
  have hrb : Star L (root b) b := fun v hv => hb _ _ (Or.inl (root_mem b)) (Or.inl hv)
  rw [transport_chart L h q hf hq (compatible_symm L hb) hrc hrb]
  unfold transport chartTransport
  group

theorem chartTransport_trans (a : V) (b c d : TrianglePoint V) :
    chartTransport h q a b c * chartTransport h q a c d = chartTransport h q a b d := by
  unfold chartTransport
  group

theorem exists_large_coordinate (b : TrianglePoint V) :
    ∃ a, 1 / (Fintype.card V + 1 : ℝ) < (b : V → ℝ) a := by
  by_contra! H
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => H a)
  have hb := (point_simplex b).2
  rw [hb,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hn : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hd : 0 < (Fintype.card V : ℝ) + 1 := by positivity
  have he := (le_div_iff₀ hd).mp (by simpa only [mul_one_div] using hs)
  linarith

theorem nearby_star {b c : TrianglePoint V} {a : V}
    (ha : 1 / (Fintype.card V + 1 : ℝ) < (b : V → ℝ) a)
    (hc : CliquePoint L c) (hbc : dist b c < 1 / (Fintype.card V + 1 : ℝ)) :
    Star L a c := by
  apply hc a
  intro he
  have hd := lt_of_le_of_lt (dist_le_pi_dist (b : V → ℝ) (c : V → ℝ) a) hbc
  rw [he, Real.dist_eq,sub_zero,abs_of_nonneg ((point_simplex b).1 a)] at hd
  exact (not_lt_of_ge ha.le) hd

theorem chartTransport_dist (a : V) (b c : TrianglePoint V) :
    dist (chartTransport h q a b c) 1 = dist (gauge h q a b) (gauge h q a c) :=
  unitary_dist_inv_mul_one _ _

theorem transport_uniform (hq : GeneralPosition h q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b c : TrianglePoint V, dist b c < δ → dist (transport h q b c) 1 < ε := by
  obtain ⟨δ,hδ,H⟩ := gauges_uniform h q hq hε
  exact ⟨δ,hδ,fun b c hbc => (chartTransport_dist h q _ b c).symm ▸ H b c hbc (root b)⟩

theorem edgeTransport_chart (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {b c d : TrianglePoint V} (hbc : Compatible L b c) (hcd : Compatible L c d)
    {a : V} (hab : Star L a b) (hac : Star L a c) (had : Star L a d) :
    edgeTransport h q b c d = chartTransport h q a b d := by
  rw [edgeTransport,transport_chart L h q hf hq hbc hab hac,
    transport_chart L h q hf hq hcd hac had,chartTransport_trans]

theorem edgeTransport_reverse (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {b c d : TrianglePoint V} (hbc : Compatible L b c) (hcd : Compatible L c d) :
    edgeTransport h q d c b = (edgeTransport h q b c d)⁻¹ := by
  rw [edgeTransport,edgeTransport,transport_reverse L h q hf hq hbc,
    transport_reverse L h q hf hq hcd,mul_inv_rev]

theorem edgeTransport_uniform (hq : GeneralPosition h q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b c d : TrianglePoint V, dist b c < δ → dist c d < δ →
      dist (edgeTransport h q b c d) 1 < ε := by
  obtain ⟨δ,hδ,H⟩ := transport_uniform h q hq (show 0 < ε/2 by positivity)
  refine ⟨δ,hδ,?_⟩
  intro b c d hbc hcd
  apply lt_of_le_of_lt (unitary_dist_mul_one_le _ _)
  have h₁ := H b c hbc
  have h₂ := H c d hcd
  linarith

/-- All three edge images in one chart have exactly trivial triangle holonomy. -/
theorem edgeTransport_triangle (hf : FlatConnection L h) (hq : GeneralPosition h q)
    (b c d u v w : TrianglePoint V) {a : V}
    (hbu : Compatible L b u) (huc : Compatible L u c)
    (hcv : Compatible L c v) (hvd : Compatible L v d)
    (hdw : Compatible L d w) (hwb : Compatible L w b)
    (hab : Star L a b) (hac : Star L a c) (had : Star L a d)
    (hau : Star L a u) (hav : Star L a v) (haw : Star L a w) :
    edgeTransport h q b u c * edgeTransport h q c v d * edgeTransport h q d w b = 1 := by
  rw [edgeTransport_chart L h q hf hq hbu huc hab hau hac,
    edgeTransport_chart L h q hf hq hcv hvd hac hav had,
    edgeTransport_chart L h q hf hq hdw hwb had haw hab]
  unfold chartTransport
  group

end Connection

end AffineTransport




end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_PathChains
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]
variable {U : Set (Set X)} (l : Local (G:=G) U)
variable (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = univ)

/-- Any multiplicative global path label is completely determined on a sufficiently
small open-cover mesh. This is the uniqueness half of low-dimensional descent. -/
theorem transport_unique (v : Cube₁ X → G)
    (hsplit : ∀ γ, v γ = v (cut₁ γ false) * v (cut₁ γ true))
    (hsmall : ∀ γ ∈ CubicalMesh.small U, v γ = l.value γ) (γ : Cube₁ X) :
    v γ = l.transport hU hcover γ := by
  suffices hh : ∀ n γ, Good₁ (U:=U) n γ → v γ = l.fold n γ by
    exact hh _ γ (depth_good hU hcover γ)
  intro n
  induction n with
  | zero => intro γ h; exact hsmall γ (good₁_zero h)
  | succ n ih =>
    intro γ h
    rw [hsplit γ,ih _ (good₁_cut h false),ih _ (good₁_cut h true)]
    rfl

end EilenbergGanea.PathTransport.Local


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_Collar
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.openDiskContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWCollar
open CubicalSingular PathTransport

theorem annulusGenerator_class (x : Annulus 2) :
    annulusOppositeInt x (MulOpposite.op (asClass (annulusGenerator x))) = Multiplicative.ofAdd 1 := by
  have he : asClass (annulusGenerator x) = ((annulusOppositeInt x).symm (Multiplicative.ofAdd 1)).unop := Quotient.out_eq _
  rw [he,MulOpposite.op_unop,MulEquiv.apply_symm_apply]

theorem annulus_loop_power (x : Annulus 2) (p : Path x x) :
    ∃ n : ℤ, MulOpposite.op (asClass p) = (MulOpposite.op (asClass (annulusGenerator x)) : (FundamentalGroup (Annulus 2) x)ᵐᵒᵖ) ^ n := by
  refine ⟨(annulusOppositeInt x (MulOpposite.op (asClass p))).toAdd,?_⟩
  apply (annulusOppositeInt x).injective
  rw [map_zpow,annulusGenerator_class]
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow]
  change _ = _ • (1 : ℤ)
  simp

theorem hurewiczOne_loop {X : Type*} [TopologicalSpace X] {r x : X}
    (q : ∀ y, Path r y) (p : Path x x) :
    hurewiczOne q (loopHomology p) = Additive.ofMul (Abelianization.of (basedPath q p)) := by
  change abHolonomyMap q (gen₁ p.toContinuousMap) = _
  rw [abHolonomyMap_gen]
  simp only [abHolonomy,holonomy_path]

theorem annulusGenerator_homology (x : Annulus 2) :
    loopHomology (annulusGenerator x) = (annulusHomologyInt x).symm 1 := by
  apply (annulusHomologyInt x).injective
  rw [LinearEquiv.apply_symm_apply]
  change annulusAbInt x (hurewiczOne _ (loopHomology _)) = 1
  rw [hurewiczOne_loop]
  have he (w : (FundamentalGroup (Annulus 2) x)ᵐᵒᵖ) :
      annulusAbInt x (Additive.ofMul (Abelianization.of w)) = (annulusOppositeInt x w).toAdd := by
    rfl
  rw [he]
  have hb := ab_based_loop (fun y => (PathConnectedSpace.joined x y).somePath) (asClass (annulusGenerator x))
  have hh := congrArg (fun z => annulusAbInt x (Additive.ofMul z)) hb
  rw [he,he] at hh
  change (annulusOppositeInt x (based _ (asClass (annulusGenerator x)))).toAdd = 1
  rw [hh,annulusGenerator_class]
  rfl

end EilenbergGanea.CWCollar


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_CellularPaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.PathTransport
open Set CubicalSingular ForestCover
variable {X G : Type*} [TopologicalSpace X] [Group G]

namespace LeftPotential
variable {U V : Set X} {r : U} {q : ∀ x : U, Path r x} {ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G}
variable (a : LeftPotential U V r q ρ)

variable (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)

theorem transport_left (γ : Cube₁ X) (hγ : Set.range γ ⊆ U) :
    a.system.transport (TwoPotential.cover_open hU hV) (TwoPotential.cover_univ hc) γ =
      ρ (holonomy q (liftCube U γ hγ)) := by
  rw [a.system.transport_small _ _ ⟨U,by simp,hγ⟩]
  exact a.value_left γ hγ

end LeftPotential

variable {U V : Set X} {r : U} (q : ∀ x : U, Path r x) (ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G)

/-- The actual finite-grid van-Kampen kernel inclusion, obtained by extending
all representations annihilating overlap loops. No presentation axiom is used. -/
theorem kernel_killed (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    (hk : KillsOverlap (V:=V) q ρ) (p : Path r r)
    (hp : (p.map continuous_subtype_val).Homotopic (Path.refl r.val)) :
    ρ (basedPath q p) = 1 := by
  let a := patched q ρ hk
  have he := a.system.transport_homotopy (TwoPotential.cover_open hU hV) (TwoPotential.cover_univ hc) hp.some
  change a.system.transport _ _ (p.map continuous_subtype_val).toContinuousMap =
    a.system.transport _ _ (ContinuousMap.const I r.val) at he
  rw [a.system.transport_const] at he
  rw [LeftPotential.transport_left a hU hV hc _ (fun _ ⟨t,ht⟩ => ht ▸ (p t).property)] at he
  have hh : liftCube U (p.map continuous_subtype_val).toContinuousMap (fun _ ⟨t,ht⟩ => ht ▸ (p t).property) = p.toContinuousMap := by
    ext t; rfl
  simpa only [hh,holonomy_path] using he

end EilenbergGanea.PathTransport

namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
variable {r : X} (q : ∀ y, Path r y)

/-- Conjugation transfers annihilation of based loops to every base point. -/
theorem kills_loops_of_root [PathConnectedSpace Y] (f : C(Y,X)) (y₀ : Y)
    (ρ : (FundamentalGroup X r)ᵐᵒᵖ →* G)
    (h : ∀ p : Path y₀ y₀, ρ (basedPath q (p.map f.continuous)) = 1)
    {y : Y} (p : Path y y) : ρ (basedPath q (p.map f.continuous)) = 1 := by
  let s := (PathConnectedSpace.joined y₀ y).somePath
  have hh := h (s.trans (p.trans s.symm))
  rw [Path.map_trans,Path.map_trans,← Path.map_symm] at hh
  simp only [basedPath_trans,basedPath_symm,map_mul,map_inv] at hh
  rw [← mul_assoc] at hh
  have he := mul_inv_eq_one.mp hh
  exact mul_left_cancel (show ρ (basedPath q (s.map f.continuous)) *
    ρ (basedPath q (p.map f.continuous)) = ρ (basedPath q (s.map f.continuous)) * 1 by simpa using he)

end EilenbergGanea.PathTransport

namespace EilenbergGanea.CWCollar
open CubicalSingular PathTransport
variable {X G : Type*} [TopologicalSpace X] [Group G] {r : X} (q : ∀ y, Path r y)

theorem kills_annulus_loops (f : C(Annulus 2,X)) (y₀ : Annulus 2)
    (ρ : (FundamentalGroup X r)ᵐᵒᵖ →* G)
    (h : ρ (basedPath q ((annulusGenerator y₀).map f.continuous)) = 1)
    {y : Annulus 2} (p : Path y y) : ρ (basedPath q (p.map f.continuous)) = 1 := by
  apply kills_loops_of_root q f y₀ ρ _ p
  intro t
  obtain ⟨n,hn⟩ := annulus_loop_power y₀ t
  have he := congrArg (ρ.comp (basedHom q f y₀)) hn
  change ρ (basedHom q f y₀ (MulOpposite.op (asClass t))) = ρ (basedHom q f y₀ (_ ^ n)) at he
  rw [map_zpow,map_zpow] at he
  change ρ (basedPath q (t.map f.continuous)) = ρ (basedPath q ((annulusGenerator y₀).map f.continuous)) ^ n at he
  rw [h,one_zpow] at he
  exact he

end EilenbergGanea.CWCollar

namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X Y J G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
variable {r : X} (q : ∀ y, Path r y)

/-- A loop in a disjoint union stays in one actual component. -/
theorem kills_sigma_loops (f : C((Σ _ : J,Y),X)) (y₀ : Y)
    (ρ : (FundamentalGroup X r)ᵐᵒᵖ →* G)
    (hk : ∀ (j : J) (y : Y) (p : Path y y),
      ρ (basedPath q (p.map (f.comp (fiberInclusion j)).continuous)) = 1)
    {z : (Σ _ : J,Y)} (p : Path z z) : ρ (basedPath q (p.map f.continuous)) = 1 := by
  let : TopologicalSpace J := ⊥
  let : DiscreteTopology J := ⟨rfl⟩
  have hi (t : I) : (p t).1 = z.1 := by
    have hc : Continuous (fun t => (p t).1) := (continuous_sigma (fun _ => continuous_const)).comp p.continuous
    have he : (p t).1 = (p 0).1 := (@inferInstance (PreconnectedSpace I)).constant hc
    exact he.trans (congrArg Sigma.fst p.source)
  let s := p.map (fiberProjection y₀ z.1).continuous
  have he := basedPath_congr q (s.map (f.comp (fiberInclusion z.1)).continuous)
    (p.map f.continuous) (fun t => by
      change f ((fiberInclusion z.1) ((fiberProjection y₀ z.1) (p t))) = f (p t)
      congr 1
      apply Sigma.ext
      · exact (hi t).symm
      · simp only [fiberInclusion,fiberProjection,ContinuousMap.coe_mk,hi t,ite_true]
        rfl)
  rw [← he]
  exact hk z.1 _ s

/-- A loop which becomes null after a map also has trivial based holonomy. -/
theorem map_basedPath_eq_one (f : C(X,Y)) {x : X} (p : Path x x)
    (hp : (p.map f.continuous).Homotopic (Path.refl (f x))) :
    (FundamentalGroup.map f r).op (basedPath q p) = 1 := by
  apply MulOpposite.unop_injective
  change asClass ((((q x).trans p).trans (q x).symm).map f.continuous) = Path.Homotopic.Quotient.refl (f r)
  rw [Path.map_trans,Path.map_trans,← Path.map_symm]
  simp only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm]
  have hh : Path.Homotopic.Quotient.mk (p.map f.continuous) = Path.Homotopic.Quotient.refl (f x) := Path.Homotopic.Quotient.eq.mpr hp
  rw [hh]
  simp only [Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.trans_symm]

end EilenbergGanea.PathTransport

namespace EilenbergGanea.CWCollar.Attachment
open Set CubicalSingular PathTransport
variable {X J : Type*} [TopologicalSpace X] (a : Attachment X J 2)
variable {r : a.outer} (q : ∀ y, Path r y) (y₀ : Annulus 2)

theorem killsOverlap_of_relators {G : Type*} [Group G]
    (ρ : (FundamentalGroup a.outer r)ᵐᵒᵖ →* G)
    (h : ∀ j, ρ (a.annulusRelator q y₀ j) = 1) : KillsOverlap (V:=a.inner) q ρ := by
  intro z p
  let f : C((Σ _ : J,Annulus 2),a.outer) := capInclusion.comp (a.annulusHomeomorph : C((Σ _ : J,Annulus 2),(a.outer ∩ a.inner : Set X)))
  let t := p.map a.annulusHomeomorph.symm.continuous
  have hh := kills_sigma_loops q f y₀ ρ (fun j y s => kills_annulus_loops q (a.annulusMap j) y₀ ρ (h j) s) t
  have he := basedPath_congr q (t.map f.continuous) (p.map capInclusion.continuous) (fun s => by
    change (⟨(a.annulusHomeomorph (a.annulusHomeomorph.symm (p s))).val,_⟩ : a.outer) = _
    exact congrArg (fun z : (a.outer ∩ a.inner : Set X) => (⟨z.val,z.property.1⟩ : a.outer)) (a.annulusHomeomorph.apply_symm_apply (p s)))
  exact (congrArg ρ he).symm.trans hh

/-- The exact ordinary attachment kernel, with one genuine annular relator per
attached2-cell. The forward inclusion uses the finite-grid patching proof. -/
theorem annulus_normalClosure (hthin : ForestCover.ThinPaths a.inner) :
    ((FundamentalGroup.map (⟨Subtype.val,continuous_subtype_val⟩ : C(a.outer,X)) r).op).ker =
      Subgroup.normalClosure (Set.range (a.annulusRelator q y₀)) := by
  let f : C(a.outer,X) := ⟨Subtype.val,continuous_subtype_val⟩
  let N := Subgroup.normalClosure (Set.range (a.annulusRelator q y₀))
  let ρ := QuotientGroup.mk' N
  apply le_antisymm
  · intro w hw
    obtain ⟨p,hp⟩ := Quotient.exists_rep w.unop
    have hp' : MulOpposite.op (asClass p) = w := by
      exact (congrArg MulOpposite.op hp).trans (MulOpposite.op_unop w)
    have hn : (p.map f.continuous).Homotopic (Path.refl r.val) := by
      apply Path.Homotopic.Quotient.eq.mp
      change ((FundamentalGroup.map f r).op (MulOpposite.op (asClass p))).unop = (1 : FundamentalGroup X r.val)
      rw [hp']
      exact congrArg MulOpposite.unop hw
    have hk : KillsOverlap (V:=a.inner) q ρ := a.killsOverlap_of_relators q y₀ ρ (fun j =>
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j,rfl⟩))
    have he := kernel_killed q ρ a.outer_open a.inner_open a.outer_union_inner hk p hn
    let u : (FundamentalGroup a.outer r)ᵐᵒᵖ := MulOpposite.op (asClass (q r))
    have hbased : basedPath q p = u * w * u⁻¹ := by
      rw [← hp']
      rfl
    rw [hbased,map_mul,map_mul,map_inv] at he
    have hh := mul_inv_eq_one.mp he
    have hf : ρ w = 1 := mul_left_cancel (show ρ u * ρ w = ρ u * 1 by simpa using hh)
    exact (QuotientGroup.eq_one_iff _).mp hf
  · apply Subgroup.normalClosure_le_normal
    rintro w ⟨j,rfl⟩
    apply map_basedPath_eq_one q f
    let g : C(Annulus 2,a.inner) := ⟨fun z => ⟨(a.annulusHomeomorph ⟨j,z⟩).val,(a.annulusHomeomorph ⟨j,z⟩).property.2⟩,
      (continuous_subtype_val.comp (a.annulusHomeomorph.continuous.comp continuous_sigmaMk)).subtype_mk _⟩
    have h := (hthin _ _ ((annulusGenerator y₀).map g.continuous) (Path.refl (g y₀))).map
      (⟨Subtype.val,continuous_subtype_val⟩ : C(a.inner,X))
    exact h

end EilenbergGanea.CWCollar.Attachment

namespace EilenbergGanea.CWCollar
open Set CubicalSingular PathTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace Attachment
variable {J : Type*} (a : Attachment X J 2)

theorem outerCapHomologyEquiv_apply [ContractibleSpace X] (c : HomologyOne (a.outer ∩ a.inner : Set X)) :
    a.outerCapHomologyEquiv c = homologyOneMap capInclusion c := by
  apply (subspaceHomologyEquiv a.outer).injective
  change (subspaceHomologyEquiv a.outer) ((subspaceHomologyEquiv a.outer).symm
    (homologyInclusion Set.inter_subset_left (subspaceHomologyEquiv (a.outer ∩ a.inner) c))) = _
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨z,rfl⟩ := (boundaries univ).mkQ_surjective c
  change (boundaries a.outer).mkQ (cycleInclusion Set.inter_subset_left (cycleMap (inc (a.outer ∩ a.inner)) _ z)) =
    (boundaries a.outer).mkQ (cycleMap (inc a.outer) _ (cycleMap capInclusion _ z))
  congr 1
  apply Subtype.ext
  change pushN₁ (inc (a.outer ∩ a.inner)) z.val = pushN₁ (inc a.outer) (pushN₁ capInclusion z.val)
  rw [← pushN₁_comp]
  rfl

/-- Each basis vector is precisely the singular class of its lifted annulus. -/
theorem annularBasis_single [ContractibleSpace X] (y₀ : Annulus 2) (j : J) :
    a.annularBasis y₀ (Finsupp.single j 1) = loopHomology ((annulusGenerator y₀).map (a.annulusMap j).continuous) := by
  change a.outerCapHomologyEquiv (homologyOneMap (a.annulusHomeomorph : C(_, _))
    (sigmaHomologyBasisMap (annulusHomologyInt y₀) (Finsupp.single j 1))) = _
  rw [outerCapHomologyEquiv_apply]
  simp only [sigmaHomologyBasisMap,Finsupp.linearCombination_single,one_smul]
  rw [← LinearMap.comp_apply,← homologyOneMap_comp,← LinearMap.comp_apply,← homologyOneMap_comp]
  rw [← annulusGenerator_homology,homologyOneMap_loop]
  rfl

end Attachment
end EilenbergGanea.CWCollar


namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X G H : Type*} [TopologicalSpace X] [Group G] [Group H]
variable {U : Set (Set X)} (l : Local (G:=G) U) (φ : G →* H)

theorem map_transport (hU : ∀ V ∈ U, IsOpen V) (hc : ⋃₀ U = univ) (γ : Cube₁ X) :
    φ (l.transport hU hc γ) = (l.map φ).transport hU hc γ := by
  apply (l.map φ).transport_unique hU hc (fun γ => φ (l.transport hU hc γ))
  · intro γ; rw [l.transport_split hU hc,map_mul]
  · intro γ h; rw [l.transport_small hU hc h]; rfl

end EilenbergGanea.PathTransport.Local


namespace EilenbergGanea.ForestCover
open Set PathTransport CubicalSingular
variable {X : Type*} [TopologicalSpace X] {r : X} (q : ∀ x, Path r x) (U V : Set X)
variable (hU : ThinPaths U) (hV : ThinPaths V)

theorem eval_rightLabel (x : X) (hx : x ∈ V) :
    evaluation q U V hU hV (rightLabel U V x) = potential q (inclusion V) ⟨x,hx⟩ * (gauge q U V x)⁻¹ := by
  by_cases hu : x ∈ U
  · rw [rightLabel_overlap U V ⟨x,hu,hx⟩]
    simp only [evaluation,FreeGroup.lift_apply_of,ZerothHomotopy.lift_mk,overlapValue,gauge,dite_eq_left hu]
  · have hnot : x ∉ U ∩ V := fun h => hu h.1
    simp only [rightLabel,dite_eq_right hnot,map_one,gauge,dite_eq_right hu,dite_eq_left hx,mul_inv_cancel]

theorem gauged_split (γ : Cube₁ X) :
    gauged q U V γ = gauged q U V (cut₁ γ false) * gauged q U V (cut₁ γ true) := by
  unfold gauged
  rw [holonomy_split q γ]
  simp only [cut₁,ContinuousMap.coe_comp,Function.comp_apply,half_false_zero,half_true_one,half_mid]
  group

theorem small_potential (W : Set X) (hW : ThinPaths W) (γ : Cube₁ X) (hγ : Set.range γ ⊆ W) :
    holonomy q γ = (potential q (inclusion W) ⟨γ 0,hγ ⟨0,rfl⟩⟩)⁻¹ *
      potential q (inclusion W) ⟨γ 1,hγ ⟨1,rfl⟩⟩ := by
  let p : Path (⟨γ 0,hγ ⟨0,rfl⟩⟩ : W) ⟨γ 1,hγ ⟨1,rfl⟩⟩ :=
    ⟨⟨fun t => ⟨γ t,hγ ⟨t,rfl⟩⟩,γ.continuous.subtype_mk _⟩,rfl,rfl⟩
  exact potential_path q hW (inclusion W) p

theorem gauged_small (γ : Cube₁ X) (hγ : γ ∈ CubicalMesh.small ({U,V} : Set (Set X))) :
    gauged q U V γ = evaluation q U V hU hV ((labels U V).value γ) := by
  rcases TwoPotential.small_either γ hγ with hγ | hγ
  · rw [(labels U V).value_left γ hγ]
    change gauged q U V γ = evaluation q U V hU hV (1⁻¹*1)
    simp only [inv_one,mul_one,map_one]
    unfold gauged
    rw [small_potential q U hU γ hγ]
    simp only [gauge,dite_eq_left (hγ ⟨0,rfl⟩),dite_eq_left (hγ ⟨1,rfl⟩)]
    group
  · rw [(labels U V).value_right γ hγ]
    change gauged q U V γ = evaluation q U V hU hV ((rightLabel U V (γ 0))⁻¹ * rightLabel U V (γ 1))
    rw [map_mul,map_inv,eval_rightLabel q U V hU hV _ (hγ ⟨0,rfl⟩),eval_rightLabel q U V hU hV _ (hγ ⟨1,rfl⟩)]
    unfold gauged
    rw [small_potential q V hV γ hγ]
    group

theorem eval_transport (hUo : IsOpen U) (hVo : IsOpen V) (hc : U ∪ V = univ) (γ : Cube₁ X) :
    evaluation q U V hU hV ((labels U V).transport hUo hVo hc γ) = gauged q U V γ := by
  rw [TwoPotential.transport,Local.map_transport]
  symm
  exact ((labels U V).system.map (evaluation q U V hU hV)).transport_unique _ _
    (gauged q U V) (gauged_split q U V) (gauged_small q U V hU hV) γ

theorem holonomy_loop_injective : Function.Injective (fun g : FundamentalGroup X r => based q g) := by
  intro g h he
  have he := congrArg MulOpposite.unop he
  let u : FundamentalGroup X r := asClass (q r)
  change u⁻¹ * (g * u) = u⁻¹ * (h * u) at he
  exact mul_right_cancel (mul_left_cancel he)

include q hU hV in
/-- A genuine two-open-set cover by spaces with simply connected components
has a free fundamental group. This includes graphs with arbitrary cell sets. -/
theorem isFree_fundamentalGroup (hUo : IsOpen U) (hVo : IsOpen V) (hc : U ∪ V = univ) :
    IsFreeGroup (FundamentalGroup X r) := by
  let f := (labels U V).system.fundamentalHom (TwoPotential.cover_open hUo hVo) (TwoPotential.cover_univ hc) r
  have hinj : Function.Injective f := by
    intro g h he
    obtain ⟨p,rfl⟩ := Quotient.exists_rep g
    obtain ⟨s,rfl⟩ := Quotient.exists_rep h
    have hv : (labels U V).transport hUo hVo hc p.toContinuousMap =
        (labels U V).transport hUo hVo hc s.toContinuousMap := MulOpposite.op_injective he
    have he' := congrArg (evaluation q U V hU hV) hv
    rw [eval_transport q U V hU hV hUo hVo hc,eval_transport q U V hU hV hUo hVo hc] at he'
    have hh : holonomy q p.toContinuousMap = holonomy q s.toContinuousMap := by
      unfold gauged at he'
      rw [show p.toContinuousMap 0 = r from p.source,show p.toContinuousMap 1 = r from p.target,
        show s.toContinuousMap 0 = r from s.source,show s.toContinuousMap 1 = r from s.target] at he'
      exact mul_left_cancel (mul_right_cancel he')
    apply holonomy_loop_injective q
    rw [holonomy_path,holonomy_path] at hh
    exact hh
  let : IsFreeGroup (FreeGroup (ZerothHomotopy (U ∩ V : Set X)))ᵐᵒᵖ :=
    IsFreeGroup.ofMulEquiv (MulEquiv.inv' _)
  exact IsFreeGroup.ofMulEquiv (MonoidHom.ofInjective hinj).symm

end EilenbergGanea.ForestCover


namespace EilenbergGanea.ForestCover
open CategoryTheory CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem thin_of_domination (f : C(X,Y)) (g : C(Y,X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (hY : ThinPaths Y) : ThinPaths X := by
  let F := FundamentalGroupoid.map f
  let G := FundamentalGroupoid.map g
  have ei : F ⋙ G ≅ 𝟭 (FundamentalGroupoid X) := by
    simpa only [F,G,← FundamentalGroupoid.map_comp,FundamentalGroupoid.map_id] using
      asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso H)
  have : F.Faithful := Functor.Faithful.of_comp_iso ei
  intro x y p q
  have he : F.map (⟦p⟧ : (FundamentalGroupoid.mk x) ⟶ FundamentalGroupoid.mk y) =
      F.map (⟦q⟧ : (FundamentalGroupoid.mk x) ⟶ FundamentalGroupoid.mk y) :=
    Quotient.sound (hY _ _ (p.map f.continuous) (q.map f.continuous))
  exact Quotient.exact (F.map_injective he)

theorem thin_discrete [DiscreteTopology X] : ThinPaths X := by
  intro x y p q
  have he : p = q := Path.ext (funext fun t => by
    have hp : p t = p 0 := (@inferInstance (PreconnectedSpace I)).constant p.continuous
    have hq : q t = q 0 := (@inferInstance (PreconnectedSpace I)).constant q.continuous
    exact hp.trans ((p.source.trans q.source.symm).trans hq.symm))
  rw [he]

theorem thin_homeomorph (e : X ≃ₜ Y) (hY : ThinPaths Y) : ThinPaths X :=
  thin_of_domination e e.symm (by
    have he : (e.symm : C(Y,X)).comp (e : C(X,Y)) = ContinuousMap.id X := ContinuousMap.ext e.left_inv
    rw [he]
    exact ContinuousMap.Homotopy.refl _) hY

end EilenbergGanea.ForestCover


namespace EilenbergGanea.ForestCover
open CubicalSingular CWCollar
variable {X J : Type*} [TopologicalSpace X] {Y : J → Type*} [∀ j, TopologicalSpace (Y j)]

theorem thin_sigma_contractible [∀ j, ContractibleSpace (Y j)] : ThinPaths (Σ j,Y j) := by
  let : TopologicalSpace J := ⊥
  let : DiscreteTopology J := ⟨rfl⟩
  let f : C((Σ j,Y j),J) := ⟨Sigma.fst,continuous_sigma (fun _ => continuous_const)⟩
  let g : C(J,(Σ j,Y j)) := ⟨fun j => ⟨j,sigmaCenter (Y:=Y) j⟩,continuous_of_discreteTopology⟩
  exact thin_of_domination f g (sigmaHomotopy (Y:=Y)).symm thin_discrete

theorem thin_outer {n : ℕ} (a : Attachment X J n) (hl : ThinPaths a.lower) : ThinPaths a.outer :=
  thin_of_domination a.retractMap a.sectionMap a.collarHomotopy.symm hl

theorem thin_inner {n : ℕ} (a : Attachment X J n) : ThinPaths a.inner :=
  thin_homeomorph a.innerHomeomorph.symm thin_sigma_contractible

include X J in
/-- Fundamental groups of arbitrary ordinary graph attachments are free. -/
theorem isFree_attachment (a : Attachment X J 1) [DiscreteTopology a.lower]
    {r : X} (q : ∀ x, Path r x) : IsFreeGroup (FundamentalGroup X r) :=
  isFree_fundamentalGroup q a.outer a.inner (thin_outer a thin_discrete) (thin_inner a)
    a.outer_open a.inner_open a.outer_union_inner

end EilenbergGanea.ForestCover


namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

/-- The ordinary zero-skeleton is discrete without any cardinality restriction. -/
theorem discrete_dim_zero (hd : ∀ k, 0 < k → IsEmpty (Cell C k)) : DiscreteTopology C := by
  apply discreteTopology_iff_forall_isOpen.mpr
  intro U
  apply (diskSum_quotient C).isOpen_preimage.mp
  rw [isOpen_sigma_iff]
  rintro ⟨n,i⟩
  have hn : n = 0 := by
    by_contra h
    have := hd n (Nat.pos_of_ne_zero h)
    exact isEmptyElim i
  subst n
  have : Subsingleton (Disk 0) := inferInstance
  exact isOpen_discrete _

end EilenbergGanea.CWSubspace

namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

theorem discrete_lower_one : DiscreteTopology (lower C 1) := by
  let S := CWComplex.skeletonLT C (1 : ℕ)
  have hd (k : ℕ) (hk : 0 < k) : IsEmpty (Cell (S : Set X) k) := by
    refine ⟨fun i => ?_⟩
    have hki : (k : ℕ∞) < 1 := by
      have hi := i.property
      simpa only [S,CWComplex.skeletonLT_I,Set.mem_ofPred_eq,Nat.cast_one] using hi
    have hkn : k < 1 := by exact_mod_cast hki
    omega
  let : DiscreteTopology (CWComplex.skeletonLT C (1 : ℕ) : Set X) := by
    exact discrete_dim_zero (S : Set X) hd
  exact (lowerHomeomorph C 1).symm.discreteTopology

end EilenbergGanea.CWSubspace

namespace EilenbergGanea.ForestCover
open Set Topology CWSubspace
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

/-- Arbitrary ordinary one-dimensional CW spaces have free fundamental groups. -/
theorem isFree_ordinary_graph (hd : ∀ k, 1 < k → IsEmpty (Cell C k))
    {r : C} (q : ∀ x, Path r x) : IsFreeGroup (FundamentalGroup C r) := by
  let : DiscreteTopology (CWSubspace.attachment C 1 hd).lower := discrete_lower_one C
  exact isFree_attachment (CWSubspace.attachment C 1 hd) q

end EilenbergGanea.ForestCover



end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_CoverTopology
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology


open Set Topology
open scoped unitInterval

namespace EilenbergGanea.CWCover
open CoverTopology
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

/-- Compatibility includes the full closed disk, not only cell interiors. -/
theorem cellLift_smul {n : ℕ} (d : deckGroup p) (c : LiftedCell (p := p) n) (z : Disk n) :
    cellLift cov (d • c) z = d • cellLift cov c z := by
  apply congrFun (cov.eq_of_comp_eq (cellLift cov (d • c)).continuous
    (d.val.continuous.comp (cellLift cov c).continuous) ?_ (diskCenter n) ?_) z
  · ext w
    change p (cellLift cov (d • c) w) = p (d • cellLift cov c w)
    rw [cellLift_project cov (d • c) w,deck_project p d (cellLift cov c w),
      cellLift_project cov c w]
    rfl
  · change cellLift cov (d • c) (diskCenter n) = d • cellLift cov c (diskCenter n)
    rw [cellLift_center,cellLift_center,liftedCell_smul_center]

end EilenbergGanea.CWCover


namespace EilenbergGanea.PathTransport
open CubicalSingular Set
variable {X : Type*} [TopologicalSpace X]
local instance instContractibleSpaceElemRealUnitInterval_solutions : ContractibleSpace I := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩

/-- A finite-mesh local-to-global principle for actual paths, preserving their
homotopy classes rather than only abelianized chains. -/
theorem path_cover_induction (U : Set (Set X)) (hU : ∀ V ∈ U, IsOpen V)
    (hc : ⋃₀ U = univ) (P : ∀ {x y : X}, Path x y → Prop)
    (hhom : ∀ {x y} {p s : Path x y}, Path.Homotopic p s → P s → P p)
    (htrans : ∀ {x y z} (p : Path x y) (s : Path y z), P p → P s → P (p.trans s))
    (hsmall : ∀ {x y} (p : Path x y), p.toContinuousMap ∈ CubicalMesh.small U → P p)
    {x y} (p : Path x y) : P p := by
  have step : ∀ n {x y} (p : Path x y), Local.Good₁ (U:=U) n p.toContinuousMap → P p := by
    intro n
    induction n with
    | zero => intro x y p hp; exact hsmall p (Local.good₁_zero hp)
    | succ n ih =>
      intro x y p hp
      let p₀ : Path x (p (half true 0)) := (halfPath₀.map p.continuous).cast p.source.symm rfl
      let p₁ : Path (p (half true 0)) y := (halfPath₁.map p.continuous).cast rfl p.target.symm
      have h₀ : P p₀ := ih p₀ (Local.good₁_cut hp false)
      have h₁ : P p₁ := ih p₁ (Local.good₁_cut hp true)
      have hh := ((SimplyConnectedSpace.paths_homotopic Path.id (halfPath₀.trans halfPath₁)).map p.toContinuousMap).pathCast p.source.symm p.target.symm
      have hid : (Path.id.map p.continuous).cast p.source.symm p.target.symm = p := Path.ext (by rfl)
      rw [hid] at hh
      exact hhom (by simpa only [Path.map_trans,Path.cast_trans] using hh) (htrans p₀ p₁ h₀ h₁)
  obtain ⟨n,hn⟩ := (Local.good₁_eventually hU hc p.toContinuousMap).exists
  exact step n p hn

end EilenbergGanea.PathTransport


namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X]

namespace Compression
variable {U V : Set X} (c : Compression U V)

theorem represents_homotopic {x y : X} {p t : Path x y} (h : p.Homotopic t)
    (ht : c.Represents t) : c.Represents p := by
  obtain ⟨s,hs⟩ := ht
  have he : asClass p = asClass t := Quotient.sound h
  exact ⟨s,by simpa only [he] using hs⟩

theorem represents_trans {x y z : X} (p : Path x y) (t : Path y z)
    (hp : c.Represents p) (ht : c.Represents t) : c.Represents (p.trans t) := by
  obtain ⟨s,hs⟩ := hp
  obtain ⟨v,hv⟩ := ht
  refine ⟨s.trans v,?_⟩
  simp only [Path.map_trans,asClass,Path.Homotopic.Quotient.mk_trans] at hs hv ⊢
  rw [← hs,← hv]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (asClass (c.bridge y)),Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.refl_trans]

theorem represents_left {x y : X} (p : Path x y) (hp : Set.range p ⊆ U) : c.Represents p := by
  have hx := hp ⟨0,p.source⟩
  have hy := hp ⟨1,p.target⟩
  let s := (subpath U (c.bridge x) (c.left x hx)).symm.trans
    ((subpath U p hp).trans (subpath U (c.bridge y) (c.left y hy)))
  refine ⟨s,?_⟩
  have he : s.map continuous_subtype_val = (c.bridge x).symm.trans (p.trans (c.bridge y)) := by
    ext t
    simp only [s,Path.map_trans,Path.trans_apply,Path.symm_apply,subpath]
    split_ifs <;> rfl
  rw [he]
  simp only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm]

theorem represents_right (hV : ForestCover.ThinPaths V) {x y : X} (p : Path x y)
    (hp : Set.range p ⊆ V) : c.Represents p := by
  have hx := hp ⟨0,p.source⟩
  have hy := hp ⟨1,p.target⟩
  have hsx : (c.select x).val ∈ V := c.right x hx ⟨1,(c.bridge x).target⟩
  have hsy : (c.select y).val ∈ V := c.right y hy ⟨1,(c.bridge y).target⟩
  let bx := subpath V (c.bridge x) (c.right x hx)
  let by' := subpath V (c.bridge y) (c.right y hy)
  let pv := subpath V p hp
  let xv : (U ∩ V : Set X) := ⟨(c.select x).val,(c.select x).property,hsx⟩
  let yv : (U ∩ V : Set X) := ⟨(c.select y).val,(c.select y).property,hsy⟩
  obtain ⟨s⟩ := c.join xv yv ⟨bx.symm.trans (pv.trans by')⟩
  let j : C((U ∩ V : Set X),V) := ⟨fun z => ⟨z.val,z.property.2⟩,continuous_subtype_val.subtype_mk _⟩
  let i : C((U ∩ V : Set X),U) := ⟨fun z => ⟨z.val,z.property.1⟩,continuous_subtype_val.subtype_mk _⟩
  let inc : C(V,X) := ⟨Subtype.val,continuous_subtype_val⟩
  have hh := (hV _ _ (bx.symm.trans (pv.trans by')) (s.map j.continuous)).map inc
  refine ⟨s.map i.continuous,?_⟩
  have he₁ : (bx.symm.trans (pv.trans by')).map inc.continuous =
      (c.bridge x).symm.trans (p.trans (c.bridge y)) := by
    rw [Path.map_trans,Path.map_trans,← Path.map_symm]
    rfl
  have he₂ : (s.map j.continuous).map inc.continuous = (s.map i.continuous).map continuous_subtype_val := Path.ext (by rfl)
  rw [he₁,he₂] at hh
  have he : asClass ((c.bridge x).symm.trans (p.trans (c.bridge y))) = asClass ((s.map i.continuous).map continuous_subtype_val) := Quotient.sound hh
  simpa only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm] using he

/-- Removing the centers of attached cells of dimension at least two does not
lose any path class, provided the actual punctured-cell components are joined. -/
theorem represents (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    (hthin : ForestCover.ThinPaths V) {x y : X} (p : Path x y) : c.Represents p :=
  path_cover_induction {U,V} (TwoPotential.cover_open hU hV) (TwoPotential.cover_univ hc)
    (fun p => c.Represents p) (fun h hp => c.represents_homotopic h hp)
    (fun p s hp hs => c.represents_trans p s hp hs) (by
      intro x y p hp
      rcases TwoPotential.small_either p.toContinuousMap hp with h | h
      · exact c.represents_left p h
      · exact c.represents_right hthin p h) p

end Compression
end EilenbergGanea.PathTransport

namespace EilenbergGanea.PathTransport.Compression
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X] {U V : Set X} (c : Compression U V)
variable (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ) (hthin : ForestCover.ThinPaths V)

include c hU hV hc hthin in
theorem pathConnected [PathConnectedSpace X] : PathConnectedSpace U where
  nonempty := ⟨c.select (Classical.choice inferInstance)⟩
  joined x y := by
    let p := (PathConnectedSpace.joined x.val y.val).somePath
    obtain ⟨s,_⟩ := c.represents hU hV hc hthin p
    let bx := subpath U (c.bridge x.val) (c.left x.val x.property)
    let by' := subpath U (c.bridge y.val) (c.left y.val y.property)
    exact ⟨bx.trans (s.trans by'.symm)⟩

include c hU hV hc hthin in
/-- Actual surjectivity on based fundamental groups, not only on H1. -/
theorem fundamental_surjective (r : U) :
    Function.Surjective (FundamentalGroup.map (⟨Subtype.val,continuous_subtype_val⟩ : C(U,X)) r) := by
  intro g
  obtain ⟨p,rfl⟩ := Quotient.exists_rep g
  obtain ⟨s,hs⟩ := c.represents hU hV hc hthin p
  let b := subpath U (c.bridge r.val) (c.left r.val r.property)
  let t : Path r r := b.trans (s.trans b.symm)
  refine ⟨asClass t,?_⟩
  change asClass (t.map continuous_subtype_val) = asClass p
  have he : t.map continuous_subtype_val = (c.bridge r.val).trans ((s.map continuous_subtype_val).trans (c.bridge r.val).symm) := by
    rw [Path.map_trans,Path.map_trans,← Path.map_symm]
    rfl
  rw [he]
  simp only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm] at hs ⊢
  rw [← hs]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  change (asClass (c.bridge r.val)).trans
    ((asClass (c.bridge r.val)).symm.trans
      ((asClass p).trans ((asClass (c.bridge r.val)).trans (asClass (c.bridge r.val)).symm))) = asClass p
  simp only [Path.Homotopic.Quotient.trans_symm]
  exact (congrArg (fun z : PQ r.val r.val => (asClass (c.bridge r.val)).trans
    ((asClass (c.bridge r.val)).symm.trans z))
      (Path.Homotopic.Quotient.trans_refl (asClass p))).trans
        ((Path.Homotopic.Quotient.trans_assoc _ _ _).symm.trans
          ((congrArg (fun z => z.trans (asClass p))
            (Path.Homotopic.Quotient.trans_symm (asClass (c.bridge r.val)))).trans
              (Path.Homotopic.Quotient.refl_trans (asClass p))))

end EilenbergGanea.PathTransport.Compression



open Classical Set


namespace EilenbergGanea.PathTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Changing the path to a circle changes its based relation by conjugacy. -/
theorem anchored_conjugate {r x : X} (q s : Path r x) (p : Path x x) :
    anchored q p = difference q s * anchored s p * (difference q s)⁻¹ := by
  apply MulOpposite.unop_injective
  change asClass ((q.trans p).trans q.symm) =
    ((asClass (q.trans s.symm)).trans (asClass ((s.trans p).trans s.symm))).trans (asClass (q.trans s.symm)).symm
  rw [show (asClass (q.trans s.symm)).symm = asClass (s.trans q.symm) by
    rw [asClass,← Path.Homotopic.Quotient.mk_symm,Path.trans_symm,Path.symm_symm]]
  simp only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk s).symm (Path.Homotopic.Quotient.mk s),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk s).symm (Path.Homotopic.Quotient.mk s),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]

end EilenbergGanea.PathTransport


namespace EilenbergGanea.CoverMonodromy
open scoped ContinuousMap
variable {X E G : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [Group G] [MulAction G E] {p : E → X}
variable (hp : IsQuotientCoveringMap p G) [SimplyConnectedSpace E] (e : E)

/-- Monodromy reads exactly the endpoint of a lifted traversal-order loop. -/
theorem traversalEquiv_loop (d : G) (γ : Path e (d • e)) :
    traversalEquiv hp e (MulOpposite.op (Path.Homotopic.Quotient.mk
      ((γ.map hp.continuous).cast rfl (hp.map_smul d).symm))) = d := by
  change (hp.fundamentalGroupToMulOpposite (⟨e,rfl⟩ : p ⁻¹' {p e})
    (Path.Homotopic.Quotient.mk ((γ.map hp.continuous).cast rfl (hp.map_smul d).symm))).unop = d
  apply MulOpposite.op_injective
  change hp.fundamentalGroupToMulOpposite (⟨e,rfl⟩ : p ⁻¹' {p e}) _ = MulOpposite.op d
  rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
  have hh := hp.isCoveringMap.monodromy_eq_of_map_eq
    (γ := Path.Homotopic.Quotient.mk ((γ.map hp.continuous).cast rfl (hp.map_smul d).symm))
    (ex := (⟨e,rfl⟩ : p ⁻¹' {p e})) (ey := (⟨d • e,hp.map_smul d⟩ : p ⁻¹' {p e}))
    (Path.Homotopic.Quotient.mk γ) (by rfl)
  exact (congrArg Subtype.val hh).symm

/-- A pair of lifted anchors differing by a deck translate records that exact
translate, independently of all anchor choices. -/
theorem traversalEquiv_difference (d : G) {z : E}
    (s : Path e (d • z)) (t : Path e z) :
    traversalEquiv hp e (MulOpposite.op (Path.Homotopic.Quotient.mk
      (((s.map hp.continuous).cast rfl (hp.map_smul d).symm).trans
        (t.map hp.continuous).symm))) = d := by
  let γ : Path e (d • e) := s.trans (t.map (hp.continuous_const_smul d)).symm
  have he : (((s.map hp.continuous).cast rfl (hp.map_smul d).symm).trans
        (t.map hp.continuous).symm) =
      ((γ.map hp.continuous).cast rfl (hp.map_smul d).symm) := by
    apply Path.ext
    funext a
    change _ = p ((s.trans (t.map (hp.continuous_const_smul d)).symm) a)
    simp only [Path.trans_apply,Path.cast_coe,Path.map_coe,Path.symm_apply]
    split_ifs <;> simp only [Function.comp_apply,hp.map_smul]
  rw [he]
  exact traversalEquiv_loop hp e d γ

end EilenbergGanea.CoverMonodromy




end

end OAI
end

section
-- module Solutions.OAIEG.Presentation_KernelCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff



namespace EilenbergGanea.PresentationAlgebra
open Classical
universe u
variable {H : Type u} {G R : Type*} [Group H] [Group G]
variable (φ : H →* G) (hf : Function.Surjective φ)
variable (r : R → H) (hr : ∀ j, φ (r j) = 1)

include hf in
/-- A kernel basis with genuine conjugate coefficients becomes the literal
Cayley relator-chain basis after choosing a free generating alphabet. -/
theorem boundary_basis_of_free [IsFreeGroup H]
    (hp : φ.ker = Subgroup.normalClosure (Set.range r))
    (B : BasedChains G R ≃ₗ[ℤ] Additive (Abelianization φ.ker))
    (hB : ∀ g j, ∃ k : H, φ k = g ∧ B (Finsupp.single (g,j) 1) =
      Additive.ofMul (Abelianization.of (⟨k*r j*k⁻¹,by
        change φ (k*r j*k⁻¹) = 1
        rw [map_mul,map_mul,map_inv,hr,mul_one,mul_inv_cancel]⟩ : φ.ker))) :
    ∃ (A : Type u) (a : A → G), Function.Surjective (wordValue a) ∧
      ∃ (s : R → FreeGroup A), (∀ j, wordValue a (s j) = 1) ∧
        (wordValue a).ker = Subgroup.normalClosure (Set.range s) ∧
        ∃ E : BasedChains G R ≃ₗ[ℤ] cycles a,
          ∀ c, (E c : BasedChains G A) = relatorChainMap a s c := by
  let A := IsFreeGroup.Generators H
  let e : FreeGroup A ≃* H := IsFreeGroup.mulEquiv H
  let a : A → G := fun x => φ (e (FreeGroup.of x))
  have ha : wordValue a = φ.comp e.toMonoidHom := by
    apply FreeGroup.ext_hom
    intro x
    simp only [wordValue,FreeGroup.lift_apply_of,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,a]
  have hsur : Function.Surjective (wordValue a) := by rw [ha]; exact hf.comp e.surjective
  let s : R → FreeGroup A := fun j => e.symm (r j)
  have hs : ∀ j, wordValue a (s j) = 1 := by
    intro j
    rw [ha]
    change φ (e (e.symm (r j))) = 1
    rw [e.apply_symm_apply,hr]
  have hnormal : (wordValue a).ker = Subgroup.normalClosure (Set.range s) := by
    change (wordValue a).ker = Subgroup.normalClosure (Set.range (e.symm ∘ r))
    rw [Set.range_comp]
    change (wordValue a).ker = Subgroup.normalClosure (e.symm.toMonoidHom '' Set.range r)
    rw [← Subgroup.map_normalClosure _ e.symm.toMonoidHom e.symm.surjective,← hp]
    ext w
    constructor
    · intro hw
      refine ⟨e w,?_,e.symm_apply_apply w⟩
      change φ (e w) = 1
      change (φ.comp e.toMonoidHom) w = 1
      rw [← ha]
      exact hw
    · rintro ⟨v,hv,rfl⟩
      change wordValue a (e.symm v) = 1
      rw [ha]
      exact (congrArg φ (e.apply_symm_apply v)).trans hv
  let ke : φ.ker ≃* (wordValue a).ker :=
    { toFun := fun k => ⟨e.symm k.val,by change wordValue a (e.symm k.val) = 1; rw [ha]; exact (congrArg φ (e.apply_symm_apply k.val)).trans k.property⟩
      invFun := fun k => ⟨e k.val,by change (φ.comp e.toMonoidHom) k.val = 1; rw [← ha]; exact k.property⟩
      left_inv := fun k => Subtype.ext (e.apply_symm_apply k.val)
      right_inv := fun k => Subtype.ext (e.symm_apply_apply k.val)
      map_mul' := fun k l => Subtype.ext (map_mul e.symm _ _) }
  let t : G → FreeGroup A := fun g => (hsur g).choose
  have ht : ∀ g, wordValue a (t g) = g := fun g => (hsur g).choose_spec
  let E : BasedChains G R ≃ₗ[ℤ] cycles a :=
    B.trans (ke.abelianizationCongr.toAdditive.toIntLinearEquiv.trans
      (KernelCycles.abKernelCycleEquiv a t ht))
  refine ⟨A,a,hsur,s,hs,hnormal,E,?_⟩
  have he : (cycles a).subtype.comp E.toLinearMap = relatorChainMap a s := by
    apply Finsupp.lhom_ext
    rintro ⟨g,j⟩ n
    rw [← Finsupp.smul_single_one (g,j) n,map_smul,map_smul]
    congr 1

    obtain ⟨k,hk,hkj⟩ := hB g j
    change (E (Finsupp.single (g,j) 1)).val = _
    change ((KernelCycles.abKernelCycleEquiv a t ht)
      (ke.abelianizationCongr.toAdditive.toIntLinearEquiv (B (Finsupp.single (g,j) 1)))).val = _
    rw [hkj]
    change pathChain a (e.symm (k*r j*k⁻¹)) 1 = relatorChainMap a s (Finsupp.single (g,j) 1)
    rw [map_mul,map_mul,map_inv,pathChain_conjugate a _ _ (hs j),one_mul,relatorChainMap_single,one_smul]
    congr 1
    rw [ha]
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using hk
  intro c
  exact LinearMap.congr_fun he c

include hf in
/-- The same literal kernel-basis criterion is invariant under a specified
isomorphism of the quotient group. No new presentation is assumed. -/
theorem boundary_basis_of_free_target [IsFreeGroup H]
    (hp : φ.ker = Subgroup.normalClosure (Set.range r))
    (B : BasedChains G R ≃ₗ[ℤ] Additive (Abelianization φ.ker))
    (hB : ∀ g j, ∃ k : H, φ k = g ∧ B (Finsupp.single (g,j) 1) =
      Additive.ofMul (Abelianization.of (⟨k*r j*k⁻¹,by
        change φ (k*r j*k⁻¹) = 1
        rw [map_mul,map_mul,map_inv,hr,mul_one,mul_inv_cancel]⟩ : φ.ker)))
    {K : Type*} [Group K] (χ : G ≃* K) :
    ∃ (A : Type u) (a : A → K), Function.Surjective (wordValue a) ∧
      ∃ (s : R → FreeGroup A), (∀ j, wordValue a (s j) = 1) ∧
        (wordValue a).ker = Subgroup.normalClosure (Set.range s) ∧
        ∃ E : BasedChains K R ≃ₗ[ℤ] cycles a,
          ∀ c, (E c : BasedChains K A) = relatorChainMap a s c := by
  let ψ := χ.toMonoidHom.comp φ
  have hψ : Function.Surjective ψ := χ.surjective.comp hf
  have hrψ : ∀ j, ψ (r j) = 1 := by intro j; change χ (φ (r j)) = 1; rw [hr,map_one]
  have hk : ψ.ker = φ.ker := by
    ext k
    change χ (φ k) = 1 ↔ φ k = 1
    exact χ.map_eq_one_iff
  let ke : φ.ker ≃* ψ.ker :=
    { toFun := fun k => ⟨k.val,by rw [hk]; exact k.property⟩
      invFun := fun k => ⟨k.val,by rw [← hk]; exact k.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let B' : BasedChains K R ≃ₗ[ℤ] Additive (Abelianization ψ.ker) :=
    (Finsupp.domLCongr (Equiv.prodCongr χ.symm.toEquiv (Equiv.refl R))).trans
      (B.trans ke.abelianizationCongr.toAdditive.toIntLinearEquiv)
  apply boundary_basis_of_free ψ hψ r hrψ (hk.trans hp) B'
  intro g j
  obtain ⟨k,hk,hkj⟩ := hB (χ.symm g) j
  refine ⟨k,?_,?_⟩
  · change χ (φ k) = g
    rw [hk,χ.apply_symm_apply]
  · simp only [B',LinearEquiv.trans_apply,Finsupp.domLCongr_single]
    change ke.abelianizationCongr.toAdditive.toIntLinearEquiv
      (B (Finsupp.single (χ.symm g,j) 1)) = _
    rw [hkj]
    rfl

end EilenbergGanea.PresentationAlgebra


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_Presentation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))

instance baseOuterConnected [PathConnectedSpace X] : PathConnectedSpace (base hd).outer :=
  (base hd).compression.pathConnected (base hd).outer_open (base hd).inner_open
    (base hd).outer_union_inner (ForestCover.thin_inner (base hd))
instance liftedOuterConnected [PathConnectedSpace E] : PathConnectedSpace (lifted cov hd).outer :=
  (lifted cov hd).compression.pathConnected (lifted cov hd).outer_open (lifted cov hd).inner_open
    (lifted cov hd).outer_union_inner (ForestCover.thin_inner (lifted cov hd))

/-- The actual collar, not an assumed graph presentation, has free π1. -/
theorem outer_isFree [PathConnectedSpace X] (r : (base hd).outer) :
    IsFreeGroup (FundamentalGroup (base hd).outer r) := by
  let a := base hd
  let S := CWComplex.skeletonLT (univ : Set X) (2 : ℕ)
  have hs (k : ℕ) (hk : 1 < k) : IsEmpty (CWSubspace.Cell (S : Set X) k) := by
    refine ⟨fun i => ?_⟩
    have hi : (k : ℕ∞) < 2 := by
      simpa only [S,CWComplex.skeletonLT_I,Set.mem_ofPred_eq,Nat.cast_ofNat] using i.property
    have hki : k < 2 := by exact_mod_cast hi
    omega
  have hr : Function.Surjective a.retractMap := fun x => ⟨a.sectionMap x,a.retract_section x⟩
  let : PathConnectedSpace a.lower := hr.pathConnectedSpace a.retractMap.continuous
  let : PathConnectedSpace (S : Set X) := inferInstanceAs (PathConnectedSpace a.lower)
  let : IsFreeGroup (FundamentalGroup a.lower (a.retractMap r)) :=
    ForestCover.isFree_ordinary_graph (S : Set X) hs (fun y => (PathConnectedSpace.joined _ y).somePath)
  let e : a.outer ≃ₕ a.lower :=
    ⟨a.retractMap,a.sectionMap,⟨a.collarHomotopy.symm⟩,by
      have he : a.retractMap.comp a.sectionMap = ContinuousMap.id a.lower := ContinuousMap.ext a.retract_section
      rw [he]⟩
  exact IsFreeGroup.ofMulEquiv (homotopyFundamentalEquiv e r).symm

variable [ContractibleSpace E]
variable (e : (lifted cov hd).outer)

variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2)

theorem kernelBasis_single (c : LiftedCell (p:=p) 2) :
    kernelBasis cov hd e q y₀ (Finsupp.single c 1) =
      Additive.ofMul (Abelianization.of (liftedKernelEquiv cov hd e
        ((lifted cov hd).annulusRelator q y₀ c))) := by
  simp only [kernelBasis,LinearEquiv.trans_apply]
  rw [Attachment.annularBasis_single,hurewiczOne_loop]
  rfl

end EilenbergGanea.CWPresentation


namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))
variable [ContractibleSpace E] (e : (lifted cov hd).outer)
variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2)

variable (hs : Function.Surjective p)

variable [PathConnectedSpace X]
/-- The selected lifted annuli give an actual presentation of the total π1. -/
theorem relator_normalClosure : (toTotal cov hd e).ker =
    Subgroup.normalClosure (Set.range (relator cov hd e q y₀ hs)) := by
  let bq : ∀ y : (base hd).outer, Path (root cov hd e) y := fun y => (PathConnectedSpace.joined _ y).somePath
  have hn := (base hd).annulus_normalClosure bq y₀ (ForestCover.thin_inner (base hd))
  apply le_antisymm
  · rw [show (toTotal cov hd e).ker = Subgroup.normalClosure (Set.range ((base hd).annulusRelator bq y₀)) from hn]
    apply Subgroup.normalClosure_le_normal
    rintro w ⟨j,rfl⟩
    let s : Path (root cov hd e) ((base hd).annulusMap j y₀) := projectedAnchor cov hd e q y₀ (chosenCell hs j)
    change anchored (bq ((base hd).annulusMap j y₀)) ((annulusGenerator y₀).map ((base hd).annulusMap j).continuous) ∈ _
    rw [anchored_conjugate (bq ((base hd).annulusMap j y₀)) s]
    exact (inferInstance : (Subgroup.normalClosure (Set.range (relator cov hd e q y₀ hs))).Normal).conj_mem _ (Subgroup.subset_normalClosure ⟨j,rfl⟩) _
  · apply Subgroup.normalClosure_le_normal
    rintro w ⟨j,rfl⟩
    exact relator_mem cov hd e q y₀ hs j

end EilenbergGanea.CWPresentation


namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))
variable [ContractibleSpace E] (e : (lifted cov hd).outer)
variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2) (hs : Function.Surjective p)

omit [ContractibleSpace E] in
theorem relator_conjugate (d : deckGroup p) (j : Cell (X:=X) 2) :
    projectedRelator cov hd e q y₀ (d • chosenCell hs j) =
      conjugator cov hd e q y₀ hs d j * relator cov hd e q y₀ hs j *
        (conjugator cov hd e q y₀ hs d j)⁻¹ :=
  anchored_conjugate _ _ _

/-- The group-ring coefficient is exactly the deck translate, not its inverse
or an arbitrary permutation. This fixes the traversal/left-action convention. -/
theorem conjugator_value (d : deckGroup p) (j : Cell (X:=X) 2) :
    deckEquiv cov hd e hs (toTotal cov hd e (conjugator cov hd e q y₀ hs d j)) = d := by
  let c := chosenCell hs j
  let z : E := ((lifted cov hd).annulusMap c y₀).val
  have hz : d • z = ((lifted cov hd).annulusMap (d • c) y₀).val := by
    let := CWCover.cwComplex cov
    change d • characteristic (X:=E) c y₀.val.val = characteristic (X:=E) (d • c) y₀.val.val
    rw [lifted_characteristic cov c,lifted_characteristic cov (d • c)]
    exact (cellLift_smul cov d c y₀.val.val).symm
  let s : Path e.val (d • z) :=
    ((q ((lifted cov hd).annulusMap (d • c) y₀)).map continuous_subtype_val).cast rfl hz
  let t : Path e.val z := (q ((lifted cov hd).annulusMap c y₀)).map continuous_subtype_val
  let hp := isQuotientCoveringMap_deck cov hs
  have he : toTotal cov hd e (conjugator cov hd e q y₀ hs d j) =
      MulOpposite.op (Path.Homotopic.Quotient.mk
        (((s.map hp.continuous).cast rfl (hp.map_smul d).symm).trans
          (t.map hp.continuous).symm)) := by
    change MulOpposite.op (Path.Homotopic.Quotient.mk
      (((projectedAnchor cov hd e q y₀ (d • c)).trans
        (projectedAnchor cov hd e q y₀ c).symm).map continuous_subtype_val)) = _
    rw [Path.map_trans,← Path.map_symm]
    rfl
  rw [he]
  exact CoverMonodromy.traversalEquiv_difference hp e.val d s t

/-- Every basis column is the literal conjugate of a selected annular relation,
with a conjugating word having precisely the specified quotient value. -/
theorem conjugateBasis_single (g : (FundamentalGroup X (p e.val))ᵐᵒᵖ) (j : Cell (X:=X) 2) :
    ∃ k : (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ,
      toTotal cov hd e k = g ∧
      conjugateBasis cov hd e q y₀ hs (Finsupp.single (g,j) 1) =
        Additive.ofMul (Abelianization.of (⟨k * relator cov hd e q y₀ hs j * k⁻¹,by
          change toTotal cov hd e (k * relator cov hd e q y₀ hs j * k⁻¹) = 1
          rw [map_mul,map_mul,map_inv,relator_mem,mul_one,mul_inv_cancel]⟩ : (toTotal cov hd e).ker)) := by
  let d := deckEquiv cov hd e hs g
  let k := conjugator cov hd e q y₀ hs d j
  refine ⟨k,?_,?_⟩
  · apply (deckEquiv cov hd e hs).injective
    exact conjugator_value cov hd e q y₀ hs d j
  · simp only [conjugateBasis,LinearEquiv.trans_apply,Finsupp.domLCongr_single]
    rw [kernelBasis_single]
    congr 2
    apply Subtype.ext
    rw [liftedKernelEquiv_val,projectedRelator_eq]
    exact relator_conjugate cov hd e q y₀ hs d j

end EilenbergGanea.CWPresentation


namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u v
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))
variable [PathConnectedSpace X] [ContractibleSpace E] (hs : Function.Surjective p)

include cov hd hs

/-- The arbitrary ordinary2-dimensional CW presentation theorem, including the
full integral boundary basis of its actual contractible cover. There are no
finiteness, countability, local finiteness, or cell-universe restrictions. -/
theorem ordinary_boundary_basis {G : Type v} [Group G] (x : X) (χ₀ : FundamentalGroup X x ≃* G) :
    ∃ (A : Type u) (a : A → G), Function.Surjective (wordValue a) ∧
      ∃ (r : Cell (X:=X) 2 → FreeGroup A), (∀ j, wordValue a (r j) = 1) ∧
        (wordValue a).ker = Subgroup.normalClosure (Set.range r) ∧
        ∃ B : BasedChains G (Cell (X:=X) 2) ≃ₗ[ℤ] cycles a,
          ∀ c, (B c : BasedChains G A) = relatorChainMap a r c := by
  let e : (lifted cov hd).outer := Classical.choice inferInstance
  let q : ∀ y : (lifted cov hd).outer, Path e y := fun y => (PathConnectedSpace.joined _ y).somePath
  let y₀ : Annulus 2 := Classical.choice inferInstance
  let H := FundamentalGroup (base hd).outer (root cov hd e)
  let : IsFreeGroup H := outer_isFree hd (root cov hd e)
  let : IsFreeGroup Hᵐᵒᵖ := IsFreeGroup.ofMulEquiv (MulEquiv.inv' H)
  have hf : Function.Surjective (toTotal cov hd e) := by
    intro g
    obtain ⟨w,hw⟩ := (base hd).compression.fundamental_surjective
      (base hd).outer_open (base hd).inner_open (base hd).outer_union_inner
      (ForestCover.thin_inner (base hd)) (root cov hd e) g.unop
    exact ⟨MulOpposite.op w,congrArg MulOpposite.op hw⟩
  let χ : (FundamentalGroup X (p e.val))ᵐᵒᵖ ≃* G :=
    (MulEquiv.inv' (FundamentalGroup X (p e.val))).symm.trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (p e.val) x).trans χ₀)
  exact PresentationAlgebra.boundary_basis_of_free_target
    (toTotal cov hd e) hf (relator cov hd e q y₀ hs)
    (relator_mem cov hd e q y₀ hs) (relator_normalClosure cov hd e q y₀ hs)
    (conjugateBasis cov hd e q y₀ hs) (conjugateBasis_single cov hd e q y₀ hs) χ

end EilenbergGanea.CWPresentation




end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Chains
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

open Classical
namespace CubicalChains
variable {G A : Type*} [Group G]

omit [Group G] in
 theorem cone_absent_upper (a : G → A) (g : G) (w : List A) (ha : a g ∉ w) :
    cone a (upperTerm g w) = -front (a g) (upperTerm g w) := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction (p := fun c _ => cone a c = -front (a g) c) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,hs,_⟩,rfl⟩
    have ha' : a g' ∉ w' := fun hm => ha (hs.subset hm)
    simp [coneTerm,ha']
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,neg_add]
  · intro n c _ hc; simp only [map_smul,hc,smul_neg]

omit [Group G] in
 theorem cone_front_present (a : G → A) (g : G) (w : List A) :
    cone a (front (a g) (upperTerm g w)) = 0 := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction
    (p := fun c _ => cone a (front (a g) c) = 0) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,_,_⟩,rfl⟩
    simp [coneTerm]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

omit [Group G] in
 theorem upper_cone_identity (a : G → A) (g : G) (w : List A)
    (hw : a g ∉ w ∨ ∃ u, w = a g :: u ∧ a g ∉ u) :
    upper (coneTerm a g w) + cone a (upperTerm g w) = Finsupp.single (g,w) 1 := by
  rcases hw with ha | ⟨u,rfl,hu⟩
  · rw [coneTerm,ite_eq_right ha,map_neg,upper_single,one_smul,upperTerm_cons,
      cone_absent_upper a g w ha,neg_sub]
    abel
  · simp only [coneTerm,List.mem_cons_self,↓reduceIte,map_zero,upperTerm_cons,
      map_sub,map_neg,cone_single,one_smul,cone_front_present,coneTerm,ite_eq_right hu]
    abel


omit [Group G] in
 theorem Removed.mem {x : A} {w u : List A} (h : Removed x w u) : x ∈ w := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  simp

omit [Group G] in
 theorem Removed.not_mem {x : A} {w u : List A} (h : Removed x w u) (hw : w.Nodup) : x ∉ u := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  rw [List.mem_append,not_or]
  refine ⟨?_,(List.nodup_cons.mp (List.nodup_append.mp hw).2.1).1⟩
  intro hx
  exact (List.nodup_append.mp hw).2.2 x hx x (by simp) rfl

variable [LinearOrder A]

namespace DescentSystem
variable {v : A → G} (D : DescentSystem v)

theorem valid_sublist {g : G} {w u : List A} (hw : D.Valid g w) (hu : u.Sublist w) : D.Valid g u :=
  ⟨hw.1.sublist hu,fun x hx => hw.2 x (hu.subset hx)⟩

theorem valid_nodup {g : G} {w : List A} (hw : D.Valid g w) : w.Nodup := hw.1.imp_of_mem (by
  intro x y _ _ h; exact ne_of_lt h)

theorem valid_removed {g : G} {w u : List A} {x : A}
    (hw : D.Valid g w) (hu : Removed x w u) : D.Valid (g*v x) u := by
  refine ⟨hw.1.sublist hu.sublist,?_⟩
  intro y hy
  exact D.preserve g x y (hw.2 x hu.mem) (hw.2 y (hu.sublist.subset hy))
    (fun he => hu.not_mem (D.valid_nodup hw) (he ▸ hy))

theorem valid_zero_length {g : G} {w : List A} (hw : D.Valid g w) (hg : D.length g = 0) : w = [] := by
  cases w with
  | nil => rfl
  | cons x w => have := D.step g x (hw.2 x (by simp)); omega

theorem choose_head {g : G} {w : List A} (hw : D.Valid g w) :
    D.choose g ∉ w ∨ ∃ u, w = D.choose g :: u ∧ D.choose g ∉ u := by
  by_cases ha : D.choose g ∈ w
  · right
    cases w with
    | nil => simp at ha
    | cons x w =>
        have hp := List.pairwise_cons.mp hw.1
        have hx : D.choose g = x := by
          rcases List.mem_cons.mp ha with h | h
          · exact h
          · exact False.elim ((not_lt_of_ge (D.choose_le g x (hw.2 x (by simp))))
              (hp.1 (D.choose g) h))
        subst x
        exact ⟨w,rfl,(List.nodup_cons.mp (D.valid_nodup hw)).1⟩
  · exact Or.inl ha

theorem valid_cone {g : G} {w : List A} (hw : D.Valid g w)
    (hg : 0 < D.length g) (ha : D.choose g ∉ w) : D.Valid g (D.choose g :: w) := by
  refine ⟨List.pairwise_cons.mpr ⟨?_,hw.1⟩,?_⟩
  · intro y hy
    exact lt_of_le_of_ne (D.choose_le g y (hw.2 y hy)) (fun he => ha (he ▸ hy))
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact D.choose_mem g hg
    · exact hw.2 y hy

theorem upperTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    upperTerm g w ∈ D.admissible (w.length-1) (D.length g) := by
  apply Finsupp.supported_mono _ (upperTerm_supported g w)
  rintro ⟨g',w'⟩ ⟨rfl,hs,hl⟩
  exact ⟨D.valid_sublist hw hs,by omega,le_rfl⟩

theorem lowerTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    lowerTerm v g w ∈ D.admissible (w.length-1) (D.length g-1) := by
  apply Finsupp.supported_mono _ (lowerTerm_supported v g w)
  rintro ⟨g',w'⟩ ⟨x,hs,rfl⟩
  have hl := D.step g x (hw.2 x hs.mem)
  exact ⟨D.valid_removed hw hs,by have := hs.length; omega,by simpa using (show D.length (g*v x) ≤ D.length g-1 by omega)⟩

theorem homotopyTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    D.homotopyTerm g w ∈ D.admissible (w.length+1) (D.length g) := by
  unfold homotopyTerm coneTerm
  split
  · exact Submodule.zero_mem _
  · rename_i hg
    split
    · exact Submodule.zero_mem _
    · rename_i ha
      apply Submodule.neg_mem
      exact Finsupp.single_mem_supported ℤ 1 ⟨D.valid_cone hw (Nat.pos_of_ne_zero hg) ha,rfl,le_rfl⟩


theorem admissible_mono {k N M : ℕ} (hNM : N ≤ M) : D.admissible k N ≤ D.admissible k M := by
  apply Finsupp.supported_mono
  rintro p ⟨hv,hk,hl⟩
  exact ⟨hv,hk,hl.trans hNM⟩

theorem upper_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    upper c ∈ D.admissible (k-1) N := by
  apply supported_map upper _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [upper_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono hN (D.upperTerm_admissible hw)

theorem lower_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    lower v c ∈ D.admissible (k-1) (N-1) := by
  apply supported_map (lower v) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [lower_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono (Nat.sub_le_sub_right hN 1) (D.lowerTerm_admissible hw)

theorem boundary_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    boundary v c ∈ D.admissible (k-1) N := by
  have h : boundary v c = upper c + lower v c := by simp [lower]
  rw [h]
  exact Submodule.add_mem _ (D.upper_admissible hc)
    (D.admissible_mono (Nat.sub_le _ _) (D.lower_admissible hc))

theorem homotopy_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    D.homotopy c ∈ D.admissible (k+1) N := by
  apply supported_map D.homotopy _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [homotopy_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono hN (D.homotopyTerm_admissible hw)

theorem boundary_squared {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    boundary v (boundary v c) = 0 := by
  rw [admissible,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => boundary v (boundary v c) = 0) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_,_⟩,rfl⟩
    simp only [boundary_single,one_smul]
    apply boundary_boundaryTerm
    exact hw.1.imp_of_mem (fun {x y} hx hy h => D.commute g x y (hw.2 x hx) (hw.2 y hy) (ne_of_lt h))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

theorem homotopy_upperTerm {g : G} (w : List A) (hg : D.length g ≠ 0) :
    D.homotopy (upperTerm g w) = cone D.choose (upperTerm g w) := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction
    (p := fun c _ => D.homotopy c = cone D.choose c) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,_,_⟩,rfl⟩
    simp only [homotopy_single,cone_single,one_smul,homotopyTerm,ite_eq_right hg]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

theorem upper_homotopy_identity {g : G} {w : List A} (hw : D.Valid g w)
    (hg : D.length g ≠ 0) :
    upper (D.homotopyTerm g w) + D.homotopy (upperTerm g w) = Finsupp.single (g,w) 1 := by
  rw [homotopyTerm,ite_eq_right hg,D.homotopy_upperTerm w hg]
  exact upper_cone_identity D.choose g w (D.choose_head hw)

theorem remainder_single {g : G} {w : List A} (hw : D.Valid g w) (hg : D.length g ≠ 0) :
    D.remainder (Finsupp.single (g,w) 1) =
      -(lower v (D.homotopyTerm g w) + D.homotopy (lowerTerm v g w)) := by
  have he := D.upper_homotopy_identity hw hg
  simp only [remainder,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.id_apply,
    homotopy_single,boundary_single,one_smul]
  simp only [lower,LinearMap.sub_apply,lowerTerm,map_sub]
  rw [← he]
  abel

theorem remainder_admissible {k N : ℕ} (hk : 0 < k) {c : Chains G A}
    (hc : c ∈ D.admissible k (N+1)) : D.remainder c ∈ D.admissible k N := by
  apply supported_map D.remainder _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk',hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk' hN
  have hpos : D.length g ≠ 0 := by
    intro hz
    have he := D.valid_zero_length hw hz
    simp only [he,List.length_nil] at hk'
    omega
  rw [D.remainder_single hw hpos]
  apply Submodule.neg_mem
  apply Submodule.add_mem
  · have hh := D.lower_admissible (D.homotopyTerm_admissible hw)
    have hNN : D.length g - 1 ≤ N := by omega
    simpa only [admissible,Nat.add_sub_cancel,hk'] using D.admissible_mono hNN hh
  · have hh := D.homotopy_admissible (D.lowerTerm_admissible hw)
    have hlen : w.length - 1 + 1 = k := by omega
    have hNN : D.length g - 1 ≤ N := by omega
    simpa only [admissible,hlen] using D.admissible_mono hNN hh

theorem admissible_zero {k : ℕ} (hk : 0 < k) : D.admissible k 0 = ⊥ := by
  apply le_antisymm _ bot_le
  suffices he : {p : G × List A | D.Valid p.1 p.2 ∧ p.2.length = k ∧ D.length p.1 ≤ 0} = ∅ by
    change Finsupp.supported ℤ ℤ _ ≤ ⊥
    rw [he,Finsupp.supported_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨g,w⟩ ⟨hw,hl,hg⟩
  dsimp only [Prod.fst,Prod.snd] at hw hl hg
  have he := D.valid_zero_length hw (by omega)
  simp only [he,List.length_nil] at hl
  omega

/-- Finite-support descending-cube contraction: every positive-dimensional
cycle bounds, with no topological exactness or contractibility assumption. -/
theorem cycle_bounds {k N : ℕ} (hk : 0 < k) (c : Chains G A)
    (hc : c ∈ D.admissible k N) (hz : boundary v c = 0) :
    ∃ b ∈ D.admissible (k+1) N, boundary v b = c := by
  induction N generalizing c with
  | zero =>
      rw [D.admissible_zero hk,Submodule.mem_bot] at hc
      subst c
      exact ⟨0,Submodule.zero_mem _,map_zero _⟩
  | succ N ih =>
      let r := D.remainder c
      have hr : r = c - boundary v (D.homotopy c) := by
        simp [r,remainder,hz]
      have hrz : boundary v r = 0 := by
        rw [hr,map_sub,hz,D.boundary_squared (D.homotopy_admissible hc),sub_zero]
      obtain ⟨b,hb,hdb⟩ := ih r (D.remainder_admissible hk hc) hrz
      refine ⟨D.homotopy c + b,Submodule.add_mem _ (D.homotopy_admissible hc)
        (D.admissible_mono (Nat.le_succ N) hb),?_⟩
      rw [map_add,hdb,hr]
      abel

end DescentSystem
end CubicalChains


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_ArtinChains
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder (Letter V)]

theorem descending_finite_bound {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    ∃ N, c ∈ (artinDescentSystem L).admissible k N := by
  refine ⟨c.support.sup (fun p => artinLength L p.1),?_⟩
  apply (Finsupp.mem_supported ℤ c).mpr
  intro p hp
  have hv := (Finsupp.mem_supported ℤ c).mp hc hp
  refine ⟨hv.1,hv.2,?_⟩
  exact Finset.le_sup (f := fun p => artinLength L p.1) hp

/-- Exactness of the genuine descending cubical chain complex in every
positive degree, with no finite-support bound imposed on the cycle. -/
theorem descending_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) (Letter V)) (hc : c ∈ descendingChains L k)
    (hz : boundary (fun x => letterValue (artinGenerator L) (invLetter x)) c = 0) :
    ∃ b ∈ descendingChains L (k+1),
      boundary (fun x => letterValue (artinGenerator L) (invLetter x)) b = c := by
  obtain ⟨N,hN⟩ := descending_finite_bound L hc
  obtain ⟨b,hb,hdb⟩ := (artinDescentSystem L).cycle_bounds hk c hN hz
  refine ⟨b,?_,hdb⟩
  apply Finsupp.supported_mono _ hb
  rintro p ⟨hv,hl,_⟩
  exact ⟨hv,hl⟩

end EilenbergGanea.TraceWords.CubeDescents

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V)

theorem origin_descent_invariant (g : ArtinGroup L) (w : Word V) (y : Letter V)
    (hw : ∀ x ∈ w, Independent L x y) :
    y ∈ rightDescents L (origin (artinGenerator L) g w) ↔ y ∈ rightDescents L g := by
  induction w generalizing g with
  | nil => rfl
  | cons x w ih =>
      have hh : ∀ z ∈ w, Independent L z y := fun z hz => hw z (by simp [hz])
      simp only [origin]
      split
      · rw [ih _ hh]
        exact descent_independent_step L g (x := (x.1,false)) (hw x (by simp))
      · exact ih _ hh

/-- Reorientation is invertible on every actual descending cube. -/
theorem orient_origin (g : ArtinGroup L) (w : Word V)
    (hw : w.Pairwise (Independent L)) (hd : ∀ x ∈ w, x ∈ rightDescents L g) :
    orient L (origin (artinGenerator L) g w) (w.map Prod.fst) = (g,w) := by
  induction w generalizing g with
  | nil => rfl
  | cons x w ih =>
      obtain ⟨hx,hwtail⟩ := List.pairwise_cons.mp hw
      have hdw : ∀ y ∈ w, y ∈ rightDescents L g := fun y hy => hd y (by simp [hy])
      have hdx := hd x (by simp)
      rcases x with ⟨q,b⟩
      cases b
      · have hp : (q,false) ∈ rightDescents L (origin (artinGenerator L) g w) :=
          (origin_descent_invariant L g w (q,false) (fun y hy => (hx y hy).symm)).mpr hdx
        simp only [origin,Bool.false_eq_true,↓reduceIte,List.map_cons,orient,ite_eq_left hp]
        rw [ih g hwtail hdw]
      · have hp : (q,false) ∉ rightDescents L (origin (artinGenerator L) (g * (artinGenerator L q)⁻¹) w) := by
          rw [origin_descent_invariant L _ w (q,false) (fun y hy => (hx y hy).symm)]
          have hh := reverse_step_descent L g (q,false)
          simpa only [letterValue,invLetter,Bool.not_false,Bool.false_eq_true,ite_false] using (not_congr hh).mpr (not_not.mpr hdx)
        simp only [origin,↓reduceIte,List.map_cons,orient,ite_eq_right hp]
        have he : origin (artinGenerator L) (g * (artinGenerator L q)⁻¹) w * artinGenerator L q =
            origin (artinGenerator L) g w := by
          rw [origin_shift]
          · group
          · intro y hy
            exact (adjacent_generators_commute L (hx y hy)).inv_left
        rw [he,ih g hwtail hdw]

end EilenbergGanea.TraceWords.CubeDescents

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder V]

attribute [local instance] OAI.EilenbergGanea.TraceWords.CubeDescents.signedLexOrder
attribute [local instance] OAI.EilenbergGanea.TraceWords.CubeDescents.signedPreorder
theorem descending_independent {g : ArtinGroup L} {w : Word V}
    (hw : (artinDescentSystem L).Valid g w) : w.Pairwise (Independent L) := by
  apply hw.1.imp_of_mem
  intro x y hx hy hlt
  exact rightDescents_pairwise L g (hw.2 x hx) (hw.2 y hy) (ne_of_lt hlt)

omit [Fintype V] [Nonempty V] in
theorem signed_sorted_iff {w : Word V} (hw : w.Pairwise (Independent L)) :
    w.Pairwise (· < ·) ↔ (w.map Prod.fst).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  constructor
  · intro hs
    exact (hs.and hw).imp (fun {x y} h => by
      have hh : toLex x < toLex y := h.1
      rcases Prod.Lex.toLex_lt_toLex.mp hh with hlt | ⟨he,_⟩
      · exact hlt
      · exact False.elim (h.2.ne he))
  · intro hs
    exact hs.imp (fun {_ _} hh => Prod.Lex.toLex_lt_toLex.mpr (Or.inl hh))

theorem normalize_descending {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) : normalize (artinGenerator L) c ∈ positiveChains L k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hv,hl⟩
  rw [normalize_single,one_smul,normalTerm]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  have hi := descending_independent L hv
  exact ⟨(signed_sorted_iff L hi).mp hv.1,by rw [List.pairwise_map]; exact hi,
    by simpa using hl⟩

theorem denormalize_positive {k : ℕ} {c : Chains (ArtinGroup L) V}
    (hc : c ∈ positiveChains L k) : denormalize L c ∈ descendingChains L k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hs,ha,hl⟩
  rw [denormalize_single,one_smul,denormalTerm]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  have hm := orient_map L g w
  have hi : (orient L g w).2.Pairwise (Independent L) := by
    rw [← hm] at ha
    rw [List.pairwise_map] at ha
    exact ha
  refine ⟨⟨(signed_sorted_iff L hi).mpr (by rw [hm]; exact hs),
    orient_descents L g w ha⟩,?_⟩
  rw [← hm,List.length_map] at hl
  exact hl

omit [Fintype V] [Nonempty V] [LinearOrder V] in
theorem normal_denormal_term (g : ArtinGroup L) (w : List V) (hw : w.Pairwise L.Adj) :
    normalize (artinGenerator L) (denormalTerm L g w) = Finsupp.single (g,w) 1 := by
  rw [denormalTerm,map_smul]
  rcases he : orient L g w with ⟨g',u⟩
  simp only [normalize_single,normalTerm,smul_smul,one_mul,sign_sq,one_smul]
  have ho := origin_orient L g w hw
  have hm := orient_map L g w
  simp only [he] at ho hm
  rw [ho,hm]

theorem denormal_normal_term {g : ArtinGroup L} {w : Word V}
    (hw : (artinDescentSystem L).Valid g w) :
    denormalize L (normalTerm (artinGenerator L) g w) = Finsupp.single (g,w) 1 := by
  simp only [normalTerm,map_smul,denormalize_single,one_smul,denormalTerm]
  rw [orient_origin L g w (descending_independent L hw) hw.2]
  simp only [smul_smul,sign_sq,one_smul]

omit [Fintype V] [Nonempty V] in
theorem normal_denormal {k : ℕ} {c : Chains (ArtinGroup L) V}
    (hc : c ∈ positiveChains L k) : normalize (artinGenerator L) (denormalize L c) = c := by
  rw [positiveChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    normalize (artinGenerator L) (denormalize L c) = c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨_,ha,_⟩,rfl⟩
    simpa only [denormalize_single,one_smul] using normal_denormal_term L g w ha
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

theorem denormal_normal {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) : denormalize L (normalize (artinGenerator L) c) = c := by
  rw [descendingChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    denormalize L (normalize (artinGenerator L) c) = c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hv,_⟩,rfl⟩
    simpa only [normalize_single,one_smul] using denormal_normal_term L hv
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

omit [Fintype V] [Nonempty V] [LinearOrder V] in
theorem step_eq_inverse_letter : step (artinGenerator L) =
    fun x => letterValue (artinGenerator L) (invLetter x) := by
  funext x
  cases hx : x.2 <;> simp [step,letterValue,invLetter,hx]

theorem descending_boundary {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    boundary (step (artinGenerator L)) c ∈ descendingChains L (k-1) := by
  obtain ⟨N,hN⟩ := descending_finite_bound L hc
  have hb := (artinDescentSystem L).boundary_admissible hN
  rw [step_eq_inverse_letter]
  apply Finsupp.supported_mono _ hb
  rintro p ⟨hv,hl,_⟩
  exact ⟨hv,hl⟩

theorem normalize_boundary {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    normalize (artinGenerator L) (boundary (step (artinGenerator L)) c) =
      boundary (artinGenerator L) (normalize (artinGenerator L) c) := by
  rw [descendingChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    normalize (artinGenerator L) (boundary (step (artinGenerator L)) c) =
      boundary (artinGenerator L) (normalize (artinGenerator L) c)) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hv,_⟩,rfl⟩
    simp only [boundary_single,normalize_single,one_smul]
    exact normalize_boundaryTerm _ g w ((descending_independent L hv).imp
      (fun {_ _} h => adjacent_generators_commute L h))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

/-- Exactness of the standard positively oriented RAAG cube chains. This is
an actual finite integral filling, derived from the descending contraction. -/
theorem positive_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) V) (hc : c ∈ positiveChains L k)
    (hz : boundary (artinGenerator L) c = 0) :
    ∃ b ∈ positiveChains L (k+1), boundary (artinGenerator L) b = c := by
  have hd := denormalize_positive L hc
  have hdz : boundary (step (artinGenerator L)) (denormalize L c) = 0 := by
    have hn : normalize (artinGenerator L)
        (boundary (step (artinGenerator L)) (denormalize L c)) = 0 := by
      rw [normalize_boundary L hd,normal_denormal L hc,hz]
    have he := denormal_normal L (descending_boundary L hd)
    rw [hn,map_zero] at he
    exact he.symm
  obtain ⟨b,hb,hdb⟩ := descending_cycle_bounds L hk (denormalize L c) hd (by rwa [← step_eq_inverse_letter])
  refine ⟨normalize (artinGenerator L) b,normalize_descending L hb,?_⟩
  rw [← normalize_boundary L hb,step_eq_inverse_letter,hdb,normal_denormal L hc]

end EilenbergGanea.TraceWords.CubeDescents


end

end OAI
end

section
-- module Solutions.OAIEG.Seed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea

theorem seed_vertex_edge_adj {v : SeedVertex} {e : SeedEdge} (h : v ∈ edgeVertices e) :
    seedGraph.Adj (.inl v) (.inr (.inl e)) := Or.inl h

theorem seed_edge_sector_adj {e : SeedEdge} {s : Sector} (h : e ∈ sectorEdges s) :
    seedGraph.Adj (.inr (.inl e)) (.inr (.inr s)) := Or.inl h

theorem rose_vertex_reachable (v : RoseVertex) :
    seedGraph.Reachable seedBase (.inl (.inl v)) := by
  rcases v with _ | ⟨b, i⟩
  · exact .refl _
  · fin_cases i
    · have h₁ : seedGraph.Adj seedBase (.inr (.inl (.inl (b, 0)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      have h₂ : seedGraph.Adj (.inl (.inl (some (b, 0))))
          (.inr (.inl (.inl (b, 0)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      exact h₁.reachable.trans h₂.reachable.symm
    · have h₁ : seedGraph.Adj seedBase (.inr (.inl (.inl (b, 2)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      have h₂ : seedGraph.Adj (.inl (.inl (some (b, 1))))
          (.inr (.inl (.inl (b, 2)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      exact h₁.reachable.trans h₂.reachable.symm

theorem seed_vertex_reachable (v : SeedVertex) :
    seedGraph.Reachable seedBase (.inl v) := by
  rcases v with v | r
  · exact rose_vertex_reachable v
  · let s := firstSector r
    have h₁ : seedGraph.Adj (.inl (.inl (sectorStart s))) (.inr (.inl (.inr s))) := by
      apply seed_vertex_edge_adj
      simp [edgeVertices]
    have h₂ : seedGraph.Adj (.inl (.inr r)) (.inr (.inl (.inr s))) := by
      apply seed_vertex_edge_adj
      simp [edgeVertices, s, firstSector]
    exact ((rose_vertex_reachable (sectorStart s)).trans h₁.reachable).trans h₂.reachable.symm

theorem seed_edge_reachable (e : SeedEdge) :
    seedGraph.Reachable seedBase (.inr (.inl e)) := by
  rcases e with e | s
  · apply (seed_vertex_reachable (.inl (circleStart e))).trans
    apply SimpleGraph.Adj.reachable
    apply seed_vertex_edge_adj
    simp [edgeVertices]
  · apply (seed_vertex_reachable (.inr s.1)).trans
    apply SimpleGraph.Adj.reachable
    apply seed_vertex_edge_adj
    simp [edgeVertices]

theorem seed_cell_reachable (x : SeedCell) : seedGraph.Reachable seedBase x := by
  rcases x with v | e
  · exact seed_vertex_reachable v
  · rcases e with e | s
    · exact seed_edge_reachable e
    · apply (seed_edge_reachable (.inl (sectorCircleEdge s))).trans
      apply SimpleGraph.Adj.reachable
      apply seed_edge_sector_adj
      simp [sectorEdges]

theorem seed_connected : seedGraph.Connected := by
  exact { preconnected := fun v w =>
    (seed_cell_reachable v).symm.trans (seed_cell_reachable w), nonempty := ⟨seedBase⟩ }


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.SeedHolonomy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

/-! Exact quaternion monodromy of the fixed presentation seed. -/
open scoped Quaternion
namespace EilenbergGanea

theorem seedGoldenReal_quadratic : 4 * seedGoldenReal ^ 2 - 2 * seedGoldenReal - 1 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [seedGoldenReal]
  nlinarith

theorem seedGoldenReal_cubic : 8 * seedGoldenReal ^ 3 - 4 * seedGoldenReal = 1 := by
  have h := seedGoldenReal_quadratic
  nlinarith [sq_nonneg (2 * seedGoldenReal - 1),
    mul_eq_zero_of_left h seedGoldenReal]

theorem seedGoldenReal_quartic : 16 * seedGoldenReal ^ 4 - 12 * seedGoldenReal ^ 2 + 1 = 0 := by
  have h := seedGoldenReal_quadratic
  have h' := seedGoldenReal_cubic
  nlinarith [mul_eq_zero_of_left h (seedGoldenReal ^ 2),
    congrArg (fun t : ℝ => t * seedGoldenReal) h']

theorem unitQuaternion_quadratic (q : ℍ) (h : Quaternion.normSq q = 1) :
    q ^ 2 = (2 * q.re : ℝ) * q - 1 := by
  have hh := Quaternion.star_mul_self q
  rw [h,Quaternion.star_eq_two_re_sub,sub_mul] at hh
  simp only [Quaternion.coe_one] at hh
  have hh' : ((2 * q.re : ℝ) : ℍ) * q = 1 + q * q := by
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hh
  rw [pow_two]
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using hh'.symm

theorem unitQuaternion_half_cube (q : ℍ) (h : Quaternion.normSq q = 1)
    (hr : q.re = 1/2) : q ^ 3 = -1 := by
  have hh := unitQuaternion_quadratic q h
  rw [hr] at hh
  norm_num at hh
  calc
    q ^ 3 = q ^ 2 * q := by rw [pow_succ]
    _ = (q - 1) * q := by rw [hh]
    _ = q ^ 2 - q := by noncomm_ring
    _ = -1 := by rw [hh]; noncomm_ring

theorem seedX_square : seedXQuaternion ^ 2 = -1 := by
  rw [pow_two]
  apply Quaternion.ext
  · rw [Quaternion.re_mul]
    norm_num [seedXQuaternion]
  · rw [Quaternion.imI_mul]
    norm_num [seedXQuaternion]
  · rw [Quaternion.imJ_mul]
    norm_num [seedXQuaternion]
  · rw [Quaternion.imK_mul]
    norm_num [seedXQuaternion]

theorem seedY_fifth : seedYQuaternion ^ 5 = -1 := by
  let q := seedYQuaternion
  let c : ℍ := (seedGoldenReal : ℝ)
  have hh : q ^ 2 = 2 * c * q - 1 := by
    simpa only [q,c,seedYQuaternion,Quaternion.coe_mul, show ((2 : ℝ) : ℍ) = 2 from rfl] using unitQuaternion_quadratic seedYQuaternion seedY_normSq
  have h3 : q ^ 3 = (4 * c ^ 2 - 1) * q - 2 * c := by
    calc
      q ^ 3 = q ^ 2 * q := by rw [pow_succ]
      _ = (2 * c * q - 1) * q := by rw [hh]
      _ = 2 * c * q ^ 2 - q := by noncomm_ring
      _ = (4 * c ^ 2 - 1) * q - 2 * c := by rw [hh]; noncomm_ring
  have h4 : q ^ 4 = (8 * c ^ 3 - 4 * c) * q - (4 * c ^ 2 - 1) := by
    calc
      q ^ 4 = q ^ 3 * q := by rw [pow_succ]
      _ = ((4 * c ^ 2 - 1) * q - 2 * c) * q := by rw [h3]
      _ = (4 * c ^ 2 - 1) * q ^ 2 - 2 * c * q := by noncomm_ring
      _ = (8 * c ^ 3 - 4 * c) * q - (4 * c ^ 2 - 1) := by rw [hh]; noncomm_ring
  have h5 : q ^ 5 = (16 * c ^ 4 - 12 * c ^ 2 + 1) * q - (8 * c ^ 3 - 4 * c) := by
    calc
      q ^ 5 = q ^ 4 * q := by rw [pow_succ]
      _ = ((8 * c ^ 3 - 4 * c) * q - (4 * c ^ 2 - 1)) * q := by rw [h4]
      _ = (8 * c ^ 3 - 4 * c) * q ^ 2 - (4 * c ^ 2 - 1) * q := by noncomm_ring
      _ = _ := by rw [hh]; noncomm_ring
  have hc3 : 8 * c ^ 3 - 4 * c = 1 := by
    change (8 : ℍ) * (seedGoldenReal : ℍ) ^ 3 - 4 * (seedGoldenReal : ℍ) = 1
    have h := congrArg (fun r : ℝ => (r : ℍ)) seedGoldenReal_cubic
    simpa only [Quaternion.coe_sub,Quaternion.coe_mul,Quaternion.coe_pow,Quaternion.coe_one,
      show ((8 : ℝ) : ℍ) = 8 from rfl, show ((4 : ℝ) : ℍ) = 4 from rfl] using h
  have hc4 : 16 * c ^ 4 - 12 * c ^ 2 + 1 = 0 := by
    change (16 : ℍ) * (seedGoldenReal : ℍ) ^ 4 - 12 * (seedGoldenReal : ℍ) ^ 2 + 1 = 0
    have h := congrArg (fun r : ℝ => (r : ℍ)) seedGoldenReal_quartic
    simpa only [Quaternion.coe_sub,Quaternion.coe_mul,Quaternion.coe_pow,Quaternion.coe_add,
      Quaternion.coe_one,Quaternion.coe_zero, show ((16 : ℝ) : ℍ) = 16 from rfl,
      show ((12 : ℝ) : ℍ) = 12 from rfl] using h
  simpa [hc3,hc4] using h5

theorem seedXYinv_cube : (seedXQuaternion * star seedYQuaternion) ^ 3 = -1 := by
  apply unitQuaternion_half_cube
  · rw [map_mul,Quaternion.normSq_star,seedX_normSq,seedY_normSq,mul_one]
  · rw [Quaternion.re_mul]
    rw [Quaternion.imI_star]
    norm_num [seedXQuaternion,seedYQuaternion]

theorem seed_unit_relations :
    seedXUnit ^ 2 = seedYUnit ^ 5 ∧
    seedXUnit ^ 2 = (seedXUnit * seedYUnit⁻¹) ^ 3 := by
  constructor
  · apply Subtype.val_injective
    change seedXQuaternion ^ 2 = seedYQuaternion ^ 5
    rw [seedX_square,seedY_fifth]
  · apply Subtype.val_injective
    change seedXQuaternion ^ 2 = (seedXQuaternion * star seedYQuaternion) ^ 3
    rw [seedX_square,seedXYinv_cube]

theorem seedRelator_unit (r : Bool) : FreeGroup.lift seedLetterUnit (seedRelator r) = 1 := by
  cases r
  · simp only [seedRelator,map_mul,map_inv,map_pow,FreeGroup.lift_apply_of,seedLetterUnit]
    rw [seed_unit_relations.1,mul_inv_cancel]
  · simp only [seedRelator,map_mul,map_inv,map_pow,FreeGroup.lift_apply_of,seedLetterUnit]
    rw [seed_unit_relations.2,mul_inv_cancel]

end EilenbergGanea



end

end OAI
end

section
-- module Solutions.OAIEG.SeedConnection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instNontrivial _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace SeedConnection

theorem boundaryWords_prod : ∀ r, (boundaryWords r).prod = seedRelator r := by
  decide

theorem circle_distinct : ∀ e : CircleEdge, circleStart e ≠ circleEnd e := by decide

theorem sector_distinct : ∀ s : Sector, sectorStart s ≠ sectorStart (nextSector s) := by decide

theorem radial_step (s : Sector) : radialLabel (nextSector s) = radialLabel s *
    (if (sectorLetter s).2 then circleLabel (sectorCircleEdge s)
      else (circleLabel (sectorCircleEdge s))⁻¹) := by
  have hs : s.2.val < (boundaryWords s.1).length := by simp
  have he := congrArg (FreeGroup.lift seedLetterUnit) (congrArg List.prod
    (List.take_succ_eq_append_getElem hs))
  rw [List.prod_append,List.prod_singleton,map_mul,boundaryWords_get] at he
  have hf : FreeGroup.lift seedLetterUnit (boundaryEdgeWord s) =
      if (sectorLetter s).2 then circleLabel (sectorCircleEdge s)
      else (circleLabel (sectorCircleEdge s))⁻¹ := by
    unfold boundaryEdgeWord circleLabel
    split <;> simp
  rw [hf] at he
  change radialLabel (nextSector s) =
    FreeGroup.lift seedLetterUnit ((boundaryWords s.1).take s.2.val).prod * _
  rw [← he]
  unfold radialLabel nextSector
  dsimp only
  by_cases hn : s.2.val + 1 < boundaryLength s.1
  · rw [Nat.mod_eq_of_lt hn]
  · have hn' : s.2.val + 1 = boundaryLength s.1 := by have hh := s.2.isLt; omega
    rw [hn',Nat.mod_self,List.take_zero,List.prod_nil,map_one,
      ← boundaryWords_length,List.take_length,boundaryWords_prod,seedRelator_unit]

theorem nextSector_first (s : Sector) : (nextSector s).1 = s.1 := rfl

theorem faceLocal_incidence (s : Sector) (e : SeedEdge) (he : e ∈ sectorEdges s)
    (v : SeedVertex) (hv : v ∈ edgeVertices e) :
    faceLocal s v = faceLocal s (edgeAnchor e) * edgeLocal e v := by
  simp only [sectorEdges,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [edgeAnchor,edgeLocal]
    · have hd := circle_distinct (sectorCircleEdge s)
      have hr := radial_step s
      cases hb : (sectorLetter s).2
      · simp only [hb,Bool.false_eq_true,↓reduceIte] at hr
        simp only [sectorStart,hb,Bool.false_eq_true,↓reduceIte,
          edgeAnchor,edgeLocal,faceLocal,Sum.inl_ne_inr,
          Sum.inl.injEq,Ne.symm hd,hd]
        rw [hr]
        group
      · simp only [hb,↓reduceIte] at hr
        simp only [sectorStart,hb,↓reduceIte,edgeAnchor,edgeLocal,faceLocal,
          Sum.inl_ne_inr,Sum.inl.injEq,Ne.symm hd]
        exact hr
  · simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [faceLocal,edgeLocal,edgeAnchor]
  · simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [faceLocal,edgeLocal,edgeAnchor,nextSector_first]
    · simp [faceLocal,edgeLocal,edgeAnchor,nextSector_first,Ne.symm (sector_distinct s)]

theorem properFace_rank {a b : SeedCell} (h : properFace a b) : cellRank a < cellRank b := by
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp only [properFace,cellRank] at * <;> omega

theorem upLabel_same_rank {a b : SeedCell} (hab : cellRank a = cellRank b) :
    upLabel a b = 1 := by
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp [upLabel,cellRank] at *

theorem upLabel_trans {a b c : SeedCell} (hab : a = b ∨ properFace a b)
    (hbc : b = c ∨ properFace b c) : upLabel a b * upLabel b c = upLabel a c := by
  rcases hab with rfl | hab
  · simp
  rcases hbc with rfl | hbc
  · simp
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    rcases c with c | (c | c) <;> simp only [properFace] at hab hbc
  simp only [upLabel,← mul_inv_rev]
  exact congrArg Inv.inv (faceLocal_incidence c b hbc a hab).symm

theorem related_symm {a b : SeedCell} : Related a b → Related b a := by
  rintro (rfl | h)
  · exact Or.inl rfl
  · exact Or.inr h.symm

theorem related_forward {a b : SeedCell} (h : Related a b) (hr : cellRank a ≤ cellRank b) :
    a = b ∨ properFace a b := by
  rcases h with h | h
  · exact Or.inl h
  rcases h with h | h
  · exact Or.inr h
  · have hd := properFace_rank h
    omega

theorem connection_reverse (a b : SeedCell) : connection b a = (connection a b)⁻¹ := by
  by_cases hab : cellRank a ≤ cellRank b
  · by_cases hba : cellRank b ≤ cellRank a
    · have he := le_antisymm hab hba
      simp [connection,hab,hba,upLabel_same_rank he,upLabel_same_rank he.symm]
    · simp [connection,hab,hba]
  · have hba : cellRank b ≤ cellRank a := (le_total _ _).resolve_left hab
    simp [connection,hab,hba]

theorem connection_flat_sorted {a b c : SeedCell} (hab : Related a b) (hbc : Related b c)
    (hrab : cellRank a ≤ cellRank b) (hrbc : cellRank b ≤ cellRank c) :
    connection a b * connection b c = connection a c := by
  simp only [connection,hrab,hrbc,le_trans hrab hrbc,↓reduceIte]
  exact upLabel_trans (related_forward hab hrab) (related_forward hbc hrbc)

theorem connection_flat {a b c : SeedCell} (hab : Related a b) (hbc : Related b c)
    (hac : Related a c) : connection a b * connection b c = connection a c := by
  by_cases hrab : cellRank a ≤ cellRank b
  · by_cases hrbc : cellRank b ≤ cellRank c
    · exact connection_flat_sorted hab hbc hrab hrbc
    · have hrcb := le_of_lt (lt_of_not_ge hrbc)
      by_cases hrac : cellRank a ≤ cellRank c
      · have H := connection_flat_sorted hac (related_symm hbc) hrac hrcb
        rw [connection_reverse b c] at H
        rw [← H]
        group
      · have hrca := le_of_lt (lt_of_not_ge hrac)
        have H := connection_flat_sorted (related_symm hac) hab hrca hrab
        rw [connection_reverse a c,connection_reverse b c] at H
        calc
          connection a b * connection b c =
              connection a c * ((connection a c)⁻¹ * connection a b) * connection b c := by group
          _ = connection a c * (connection b c)⁻¹ * connection b c := by rw [H]
          _ = connection a c := by group
  · have hrba := le_of_lt (lt_of_not_ge hrab)
    by_cases hrac : cellRank a ≤ cellRank c
    · have H := connection_flat_sorted (related_symm hab) hac hrba hrac
      rw [connection_reverse a b] at H
      rw [← H]
      group
    · have hrca := le_of_lt (lt_of_not_ge hrac)
      by_cases hrbc : cellRank b ≤ cellRank c
      · have H := connection_flat_sorted hbc (related_symm hac) hrbc hrca
        rw [connection_reverse a c,connection_reverse a b] at H
        calc
          connection a b * connection b c =
              connection a b * (connection b c * (connection a c)⁻¹) * connection a c := by group
          _ = connection a b * (connection a b)⁻¹ * connection a c := by rw [H]
          _ = connection a c := by group
      · have hrcb := le_of_lt (lt_of_not_ge hrbc)
        have H := connection_flat_sorted (related_symm hbc) (related_symm hab) hrcb hrba
        rw [connection_reverse b c,connection_reverse a b,connection_reverse a c] at H
        have H' := congrArg Inv.inv H
        simpa only [mul_inv_rev,inv_inv] using H'

theorem adjacent_rank_ne {a b : SeedCell} (h : seedGraph.Adj a b) : rankFin a ≠ rankFin b := by
  intro he
  have he' := congrArg Fin.val he
  change cellRank a = cellRank b at he'
  rcases h with h | h <;> have hh := properFace_rank h <;> omega

theorem clique_card_le_three (s : Finset SeedCell) (hs : (s : Set SeedCell).Pairwise seedGraph.Adj) :
    s.card ≤ 3 := by
  have hi : Set.InjOn rankFin (s : Set SeedCell) := by
    intro a ha b hb he
    by_contra hn
    exact adjacent_rank_ne (hs ha hb hn) he
  have hc := Finset.card_le_card (Finset.subset_univ (s.image rankFin))
  rwa [Finset.card_image_of_injOn hi,Finset.card_univ,Fintype.card_fin] at hc

theorem roseLoop_holonomy : (List.zipWith connection roseLoop roseLoop.tail).prod = seedXUnit := by
  simp [roseLoop,connection,cellRank,upLabel,edgeLocal,circleLabel,circleWord,
    circleStart,seedLetterUnit]

theorem roseLoop_nontrivial : (List.zipWith connection roseLoop roseLoop.tail).prod ≠ 1 := by
  rw [roseLoop_holonomy]
  intro h
  have hh := congrArg (fun q : SeedSU2 => (q : ℍ).re) h
  norm_num [seedXUnit,seedXQuaternion] at hh

end SeedConnection



end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.LevelTransport
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace LevelTransport
open TraceWords AffineTransport

variable {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
variable (hdim : ∀ s : Finset V, (s : Set V).Pairwise L.Adj → s.card ≤ 3)

theorem point_mem_support (g : ArtinGroup L) (hg : 0 < traceLength L (artinNormalTrace L g))
    {v : V} (hv : (point L hdim g hg : V → ℝ) v ≠ 0) :
    v ∈ (traceCounts L (artinNormalTrace L g)).support := by
  by_contra h
  have he := Finsupp.notMem_support_iff.mp h
  exact hv (by simp [point,artinDirection,traceDirection,he])

theorem point_clique (g : ArtinGroup L) (hg : 0 < traceLength L (artinNormalTrace L g)) :
    CliquePoint L (point L hdim g hg) := by
  intro a ha v hv
  by_cases hav : a = v
  · exact Or.inl hav
  · exact Or.inr (traceCounts_support_clique L _
      (point_mem_support L hdim g hg ha) (point_mem_support L hdim g hg hv) hav)

/-- Both hypotheses refer to actual reduced Artin lengths, not an assumed word metric. -/
theorem point_step (g : ArtinGroup L) (x : Letter V)
    (hg : 0 < traceLength L (artinNormalTrace L g))
    (hgx : 0 < traceLength L (artinNormalTrace L (g * letterValue (artinGenerator L) x)))
    (N : ℕ) (hNg : N ≤ traceLength L (artinNormalTrace L g))
    (hNgx : N ≤ traceLength L (artinNormalTrace L (g * letterValue (artinGenerator L) x))) :
    Compatible L (point L hdim g hg) (point L hdim (g * letterValue (artinGenerator L) x) hgx) ∧
    dist (point L hdim g hg) (point L hdim (g * letterValue (artinGenerator L) x) hgx) ≤
      2 / (N+1 : ℝ) := by
  classical
  obtain ⟨hs,n,_,hn,hbd⟩ := artinDirection_right_step L g x hg hgx
  have hNn : N ≤ n := by rcases hn with ⟨he,_⟩ | ⟨he,_⟩ <;> omega
  constructor
  · intro v w hv hw
    by_cases he : v = w
    · exact Or.inl he
    · apply Or.inr
      apply hs _ _ he
      · rcases hv with hv | hv
        · exact Finset.mem_union_left _ (point_mem_support L hdim g hg hv)
        · exact Finset.mem_union_right _ (point_mem_support L hdim _ hgx hv)
      · rcases hw with hw | hw
        · exact Finset.mem_union_left _ (point_mem_support L hdim g hg hw)
        · exact Finset.mem_union_right _ (point_mem_support L hdim _ hgx hw)
  · have hc : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hNn 1
    have hd : 0 < (N : ℝ) + 1 := by positivity
    have hfrac : 2 / (n+1 : ℝ) ≤ 2 / (N+1 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hd hc
    apply le_trans ?_ hfrac
    change dist (artinDirection L g) (artinDirection L (g * letterValue (artinGenerator L) x)) ≤ _
    apply (dist_pi_le_iff (by positivity)).mpr
    intro v
    rw [Real.dist_eq,abs_sub_comm]
    exact le_trans (Finset.single_le_sum (fun w _ => abs_nonneg (artinDirection L (g * letterValue (artinGenerator L) x) w - artinDirection L g w)) (Finset.mem_univ v)) hbd


omit [Fintype V] [LinearOrder V] in
theorem edgeVertex_reverse (N : ℕ) (g : NegativeLevel L N) (q r : V) :
    edgeVertex L N (edgeVertex L N g q r) r q = g := by
  apply Subtype.ext
  change (g : ArtinGroup L) * _ * _ * _ * _ = _
  group

omit [Fintype V] [LinearOrder V] in
theorem upperVertex_reverse (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (q r : V) :
    upperVertex L N hN (edgeVertex L N g q r) r = upperVertex L N hN g q := by
  apply Subtype.ext
  dsimp only [edgeVertex,upperVertex]
  group

theorem upperPoint_step (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (v : V) :
    Compatible L (levelPoint L hdim N (by omega) g)
      (levelPoint L hdim (N-1) (by omega) (upperVertex L N hN g v)) ∧
    dist (levelPoint L hdim N (by omega) g)
      (levelPoint L hdim (N-1) (by omega) (upperVertex L N hN g v)) ≤ 2 / (N : ℝ) := by
  let hu := upperVertex L N hN g v
  have hlen := negative_level_length L N g.property
  have hlen' := negative_level_length L (N-1) hu.property
  dsimp only [hu,upperVertex] at hlen'
  have H := point_step L hdim (g : ArtinGroup L) (v,true)
    (lt_of_lt_of_le (by omega : 0 < N) hlen)
    (by simpa only [letterValue_positive] using lt_of_lt_of_le (by omega : 0 < N-1) hlen')
    (N-1) (le_trans (Nat.sub_le N 1) hlen)
    (by simpa only [letterValue_positive] using hlen')
  have he : ((N-1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast (show (N-1 : ℕ) + 1 = N by omega)
  simpa only [levelPoint,upperVertex,letterValue_positive,he] using H

variable (h : V → V → SU2) (Q : V → ℍ)

theorem edgeLabel_reverse (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (q r : V) :
    edgeLabel L hdim h Q N hN (edgeVertex L N g q r) r q =
      (edgeLabel L hdim h Q N hN g q r)⁻¹ := by
  have h₁ := (upperPoint_step L hdim N hN g q).1
  have h₂ := (upperPoint_step L hdim N hN (edgeVertex L N g q r) r).1
  rw [upperVertex_reverse] at h₂
  unfold edgeLabel
  rw [edgeVertex_reverse,upperVertex_reverse]
  exact edgeTransport_reverse L h Q hf hQ h₁ (compatible_symm L h₂)

theorem edgeLabel_uniform (hQ : GeneralPosition h Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → ∀ hN : 1 < N, ∀ g : NegativeLevel L N, ∀ q r : V,
      dist (edgeLabel L hdim h Q N hN g q r) 1 < ε := by
  obtain ⟨δ,hδ,H⟩ := edgeTransport_uniform h Q hQ hε
  obtain ⟨M,hM⟩ := exists_nat_gt (2 / δ)
  refine ⟨M,?_⟩
  intro N hMN hN g q r
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbound : 2 / (N : ℝ) < δ := by
    apply (div_lt_iff₀ hN0).mpr
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hh := (div_lt_iff₀ hδ).mp hM
    nlinarith
  apply H
  · exact lt_of_le_of_lt (upperPoint_step L hdim N hN g q).2 hbound
  · have hh := (upperPoint_step L hdim N hN (edgeVertex L N g q r) r).2
    rw [upperVertex_reverse,dist_comm] at hh
    exact lt_of_le_of_lt hh hbound


omit [LinearOrder V] in
/-- Six compatible generator pieces around a level triangle lie in one flat chart
once the three edge images are uniformly short. -/
theorem triangle_of_short (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (b c d u v w : TrianglePoint V) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : 4 * δ < 1 / (Fintype.card V + 1 : ℝ))
    (hb : CliquePoint L b) (hc : CliquePoint L c) (hd : CliquePoint L d)
    (hu : CliquePoint L u) (hv : CliquePoint L v) (hw : CliquePoint L w)
    (hbu : Compatible L b u) (huc : Compatible L u c)
    (hcv : Compatible L c v) (hvd : Compatible L v d)
    (hdw : Compatible L d w) (hwb : Compatible L w b)
    (dbu : dist b u ≤ δ) (duc : dist u c ≤ δ)
    (dcv : dist c v ≤ δ) (dvd : dist v d ≤ δ)
    (_ddw : dist d w ≤ δ) (dwb : dist w b ≤ δ) :
    edgeTransport h Q b u c * edgeTransport h Q c v d * edgeTransport h Q d w b = 1 := by
  have dbc : dist b c ≤ 2 * δ := by linarith [dist_triangle b u c]
  have dbv : dist b v ≤ 3 * δ := by linarith [dist_triangle b c v]
  have dbd : dist b d ≤ 4 * δ := by linarith [dist_triangle b v d]
  have dbw : dist b w ≤ δ := by simpa only [dist_comm] using dwb
  obtain ⟨a,ha⟩ := exists_large_coordinate b
  apply edgeTransport_triangle L h Q hf hQ b c d u v w hbu huc hcv hvd hdw hwb
  · exact nearby_star L ha hb (by simpa using lt_of_lt_of_le hδ (le_of_lt (by linarith : δ < 1 / (Fintype.card V + 1 : ℝ))))
  · exact nearby_star L ha hc (by linarith)
  · exact nearby_star L ha hd (lt_of_le_of_lt dbd hsmall)
  · exact nearby_star L ha hu (by linarith)
  · exact nearby_star L ha hv (by linarith)
  · exact nearby_star L ha hw (by linarith)

/-- Every oriented three-edge loop with these actual level endpoints is flat.
In particular both kinds of sections of a three-cube are covered. -/
theorem edgeLabel_triangle (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) (hsize : 8 / (N : ℝ) < 1 / (Fintype.card V + 1 : ℝ))
    (g₀ g₁ g₂ : NegativeLevel L N) (q₀ r₀ q₁ r₁ q₂ r₂ : V)
    (e₀ : edgeVertex L N g₀ q₀ r₀ = g₁)
    (e₁ : edgeVertex L N g₁ q₁ r₁ = g₂)
    (e₂ : edgeVertex L N g₂ q₂ r₂ = g₀) :
    edgeLabel L hdim h Q N hN g₀ q₀ r₀ *
      edgeLabel L hdim h Q N hN g₁ q₁ r₁ *
      edgeLabel L hdim h Q N hN g₂ q₂ r₂ = 1 := by
  have h₀ := upperPoint_step L hdim N hN g₀ q₀
  have h₁ := upperPoint_step L hdim N hN g₁ q₁
  have h₂ := upperPoint_step L hdim N hN g₂ q₂
  have j₀ := upperPoint_step L hdim N hN g₁ r₀
  have j₁ := upperPoint_step L hdim N hN g₂ r₁
  have j₂ := upperPoint_step L hdim N hN g₀ r₂
  rw [← e₀,upperVertex_reverse,e₀] at j₀
  rw [← e₁,upperVertex_reverse,e₁] at j₁
  rw [← e₂,upperVertex_reverse,e₂] at j₂
  unfold edgeLabel
  rw [e₀,e₁,e₂]
  apply triangle_of_short L h Q hf hQ _ _ _ _ _ _ (2/(N : ℝ))
  · positivity
  · convert hsize using 1; ring
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact h₀.1
  · exact compatible_symm L j₀.1
  · exact h₁.1
  · exact compatible_symm L j₁.1
  · exact h₂.1
  · exact compatible_symm L j₂.1
  · exact h₀.2
  · simpa only [dist_comm] using j₀.2
  · exact h₁.2
  · simpa only [dist_comm] using j₁.2
  · exact h₂.2
  · simpa only [dist_comm] using j₂.2


theorem star_vertex {a v : V} (hav : Related L a v) : Star L a (vertexPoint v) := by
  intro w hw
  have he : v = w := by by_contra hh; exact hw (by simp [vertexPoint,hh])
  simpa only [← he] using hav

omit [Fintype V] [LinearOrder V] in
theorem negative_powers_upper {q r : V} (hqr : L.Adj q r) (n m : ℕ) :
    (artinGenerator L q)⁻¹ ^ (n+1) * (artinGenerator L r)⁻¹ ^ m * artinGenerator L q =
      (artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m := by
  have hc := (adjacent_generators_commute L hqr).inv_right.pow_right m
  calc
    _ = (artinGenerator L q)⁻¹ ^ n *
        ((artinGenerator L q)⁻¹ * ((artinGenerator L r)⁻¹ ^ m * artinGenerator L q)) := by
      simp only [pow_succ]; group
    _ = (artinGenerator L q)⁻¹ ^ n *
        ((artinGenerator L q)⁻¹ * (artinGenerator L q * (artinGenerator L r)⁻¹ ^ m)) := by
      rw [← hc.eq]
    _ = _ := by group

/-- Negative commuting powers remain exactly in their two-coordinate face. -/
theorem powersPoint_star {q r : V} (hqr : L.Adj q r) (n m : ℕ)
    (hg : 0 < traceLength L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m))) :
    Star L q (point L hdim ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m) hg) := by
  intro v hv
  by_cases hqv : q = v
  · exact Or.inl hqv
  by_cases hrv : r = v
  · exact Or.inr (hrv ▸ hqr)
  exfalso
  apply hv
  rw [point_val,direction_negative_commuting_powers L hqr]
  simp [hqv,hrv]

/-- Constant endpoint in the q-direction, stated with a concrete positive height. -/
theorem powersPoint_first {q r : V} (hqr : L.Adj q r) (N : ℕ) (hN : 0 < N)
    (hg : 0 < traceLength L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ N * (artinGenerator L r)⁻¹ ^ 0))) :
    point L hdim ((artinGenerator L q)⁻¹ ^ N * (artinGenerator L r)⁻¹ ^ 0) hg =
      vertexPoint q := by
  apply Subtype.ext
  funext v
  rw [point_val,vertexPoint_val,direction_negative_commuting_powers L hqr]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  by_cases hv : q = v <;> simp [hv,hn]

theorem powersPoint_last {q r : V} (hqr : L.Adj q r) (N : ℕ) (hN : 0 < N)
    (hg : 0 < traceLength L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ 0 * (artinGenerator L r)⁻¹ ^ N))) :
    point L hdim ((artinGenerator L q)⁻¹ ^ 0 * (artinGenerator L r)⁻¹ ^ N) hg =
      vertexPoint r := by
  apply Subtype.ext
  funext v
  rw [point_val,vertexPoint_val,direction_negative_commuting_powers L hqr]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  by_cases hv : r = v <;> simp [hv,hn]

omit [Fintype V] [LinearOrder V] in
theorem powerVertex_step (N : ℕ) {q r : V} (hqr : L.Adj q r) {j : ℕ} (hj : j < N) :
    edgeVertex L N (powerVertex L N q r j) q r = powerVertex L N q r (j+1) := by
  apply Subtype.ext
  dsimp only [powerVertex,edgeVertex]
  rw [min_eq_left (by omega : j ≤ N),min_eq_left (by omega : j+1 ≤ N)]
  have he : N-j = (N-(j+1))+1 := by omega
  rw [he,negative_powers_upper L hqr,pow_succ]
  group

omit [Fintype V] [LinearOrder V] in
theorem powerVertex_upper (N : ℕ) (hN : 1 < N) {q r : V}
    (hqr : L.Adj q r) {j : ℕ} (hj : j < N) :
    (upperVertex L N hN (powerVertex L N q r j) q : ArtinGroup L) =
      (artinGenerator L q)⁻¹ ^ (N-(j+1)) * (artinGenerator L r)⁻¹ ^ j := by
  dsimp only [powerVertex,upperVertex]
  rw [min_eq_left (by omega : j ≤ N)]
  have he : N-j = (N-(j+1))+1 := by omega
  rw [he,negative_powers_upper L hqr]

theorem powerVertex_star (N : ℕ) (hN : 0 < N) {q r : V} (hqr : L.Adj q r) (j : ℕ) :
    Star L q (levelPoint L hdim N hN (powerVertex L N q r j)) :=
  powersPoint_star L hdim hqr _ _ _

theorem powerVertex_upper_star (N : ℕ) (hN : 1 < N) {q r : V}
    (hqr : L.Adj q r) {j : ℕ} (hj : j < N) :
    Star L q (levelPoint L hdim (N-1) (by omega)
      (upperVertex L N hN (powerVertex L N q r j) q)) := by
  unfold levelPoint
  generalize_proofs hpos
  simp only [powerVertex_upper L N hN hqr hj] at hpos ⊢
  exact powersPoint_star L hdim hqr _ _ _

theorem powerLabel_chart (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q r : V} (hqr : L.Adj q r) {j : ℕ} (hj : j < N) :
    edgeLabel L hdim h Q N hN (powerVertex L N q r j) q r =
      chartTransport h Q q (levelPoint L hdim N (by omega) (powerVertex L N q r j))
        (levelPoint L hdim N (by omega) (powerVertex L N q r (j+1))) := by
  have hb := upperPoint_step L hdim N hN (powerVertex L N q r j) q
  have hc := upperPoint_step L hdim N hN (edgeVertex L N (powerVertex L N q r j) q r) r
  rw [upperVertex_reverse] at hc
  unfold edgeLabel
  rw [edgeTransport_chart L h Q hf hQ hb.1 (compatible_symm L hc.1)
    (powerVertex_star L hdim N (by omega) hqr j) (powerVertex_upper_star L hdim N hN hqr hj)]
  · rw [powerVertex_step L N hqr hj]
  · rw [powerVertex_step L N hqr hj]
    exact powerVertex_star L hdim N (by omega) hqr (j+1)


/-- The entire subdivided edge has the exact endpoint transport, not merely a limit. -/
theorem exists_powerWalk (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q r : V} (hqr : L.Adj q r) (k : ℕ) (hk : k ≤ N) :
    ∃ p : Walk L N (powerVertex L N q r 0) (powerVertex L N q r k),
      walkProduct L hdim h Q N hN p =
        chartTransport h Q q (levelPoint L hdim N (by omega) (powerVertex L N q r 0))
          (levelPoint L hdim N (by omega) (powerVertex L N q r k)) := by
  induction k with
  | zero => exact ⟨.nil _,by simp [chartTransport]⟩
  | succ k ih =>
      obtain ⟨p,hp⟩ := ih (by omega)
      let t : Walk L N (powerVertex L N q r k)
          (edgeVertex L N (powerVertex L N q r k) q r) := .cons q r hqr (.nil _)
      let t' := t.cast rfl (powerVertex_step L N hqr (by omega : k < N))
      refine ⟨p.append t',?_⟩
      rw [walkProduct_append,hp]
      simp only [t',walkProduct_cast,t,walkProduct_cons,walkProduct_nil,mul_one]
      rw [powerLabel_chart L hdim h Q hf hQ N hN hqr (by omega),chartTransport_trans]

omit [Fintype V] [LinearOrder V] in
theorem powerVertex_zero (N : ℕ) (q r : V) :
    powerVertex L N q r 0 = pureVertex L N q := by apply Subtype.ext; simp [powerVertex,pureVertex]

omit [Fintype V] [LinearOrder V] in
theorem powerVertex_last (N : ℕ) (q r : V) :
    powerVertex L N q r N = pureVertex L N r := by apply Subtype.ext; simp [powerVertex,pureVertex]

theorem levelPoint_power_zero (N : ℕ) (hN : 0 < N) {q r : V} (hqr : L.Adj q r) :
    levelPoint L hdim N hN (powerVertex L N q r 0) = vertexPoint q := by
  unfold levelPoint
  have hh : (powerVertex L N q r 0 : ArtinGroup L) =
      (artinGenerator L q)⁻¹ ^ N * (artinGenerator L r)⁻¹ ^ 0 := by simp [powerVertex]
  simp only [hh]
  exact powersPoint_first L hdim hqr N hN _

theorem levelPoint_power_last (N : ℕ) (hN : 0 < N) {q r : V} (hqr : L.Adj q r) :
    levelPoint L hdim N hN (powerVertex L N q r N) = vertexPoint r := by
  unfold levelPoint
  have hh : (powerVertex L N q r N : ArtinGroup L) =
      (artinGenerator L q)⁻¹ ^ 0 * (artinGenerator L r)⁻¹ ^ N := by simp [powerVertex]
  simp only [hh]
  exact powersPoint_last L hdim hqr N hN _

theorem exists_expanded_edge (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q r : V} (hqr : L.Adj q r) :
    ∃ p : Walk L N (pureVertex L N q) (pureVertex L N r),
      walkProduct L hdim h Q N hN p =
        (vertexGauge h Q q)⁻¹ * h q r * vertexGauge h Q r := by
  obtain ⟨p,hp⟩ := exists_powerWalk L hdim h Q hf hQ N hN hqr N le_rfl
  refine ⟨p.cast (powerVertex_zero L N q r) (powerVertex_last L N q r),?_⟩
  rw [walkProduct_cast,hp,levelPoint_power_zero L hdim N (by omega) hqr,
    levelPoint_power_last L hdim N (by omega) hqr]
  unfold chartTransport vertexGauge
  rw [gauge_transition L h Q hf hQ (Or.inr hqr)
    (star_vertex L (Or.inr hqr)) (star_vertex L (Or.inl rfl))]
  group

theorem exists_expanded_walk (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q r : V} (w : L.Walk q r) :
    ∃ p : Walk L N (pureVertex L N q) (pureVertex L N r),
      walkProduct L hdim h Q N hN p =
        (vertexGauge h Q q)⁻¹ * graphWalkProduct L h w * vertexGauge h Q r := by
  induction w with
  | nil => exact ⟨.nil _,by simp [graphWalkProduct]⟩
  | @cons q t r hqt w ih =>
      obtain ⟨p,hp⟩ := exists_expanded_edge L hdim h Q hf hQ N hN hqt
      obtain ⟨s,hs⟩ := ih
      refine ⟨p.append s,?_⟩
      rw [walkProduct_append,hp,hs]
      simp only [graphWalkProduct]
      group

omit [Fintype V] [LinearOrder V] in
theorem graphWalkProduct_eq_zipWith {a b : V} (w : L.Walk a b) :
    graphWalkProduct L h w = (List.zipWith h w.support w.support.tail).prod := by
  induction w with
  | nil => simp [graphWalkProduct]
  | @cons q t r hqt w ih =>
      cases w with
      | nil => simp [graphWalkProduct]
      | cons htl p => simpa only [graphWalkProduct,SimpleGraph.Walk.support_cons,
          List.tail_cons,List.zipWith_cons_cons,List.prod_cons] using congrArg (h q t * ·) ih

/-- A nontrivial seed holonomy survives every sufficiently translated level. -/
theorem exists_nontrivial_level_walk (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q : V} (w : L.Walk q q)
    (hw : graphWalkProduct L h w ≠ 1) :
    ∃ p : Walk L N (pureVertex L N q) (pureVertex L N q),
      walkProduct L hdim h Q N hN p ≠ 1 := by
  obtain ⟨p,hp⟩ := exists_expanded_walk L hdim h Q hf hQ N hN w
  refine ⟨p,?_⟩
  rw [hp]
  intro he
  apply hw
  calc
    graphWalkProduct L h w = vertexGauge h Q q *
      ((vertexGauge h Q q)⁻¹ * graphWalkProduct L h w * vertexGauge h Q q) *
        (vertexGauge h Q q)⁻¹ := by group
    _ = 1 := by rw [he]; group


theorem walkProduct_eq_eval (N : ℕ) (hN : 1 < N) {g k : NegativeLevel L N}
    (p : Walk L N g k) :
    walkProduct L hdim h Q N hN p = p.eval (edgeLabel L hdim h Q N hN) := by
  induction p with
  | nil => rfl
  | cons q r hqr p ih => simp only [walkProduct,Walk.eval,ih]

end LevelTransport

namespace SourceTransport
open LevelTransport AffineTransport

theorem seedWalk_support : seedWalk.support = SeedConnection.roseLoop :=
  SimpleGraph.Walk.support_ofSupport _ _

theorem seedWalk_product_ne : graphWalkProduct seedGraph SeedConnection.connection seedWalk ≠ 1 := by
  rw [graphWalkProduct_eq_zipWith,seedWalk_support]
  exact SeedConnection.roseLoop_nontrivial

/-- Actual small flat transport for the fixed source level graph. There are no
representation, direction-map, local-chart, or nontriviality hypotheses here. -/
theorem source_small_labels (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 < N ∧ ∃ a : NegativeLevel seedGraph N → SeedCell → SeedCell → SU2,
      (∀ g q r, a (edgeVertex seedGraph N g q r) r q = (a g q r)⁻¹) ∧
      (∀ g q r, dist (a g q r) 1 < ε) ∧
      (∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
        edgeVertex seedGraph N g₀ q₀ r₀ = g₁ →
        edgeVertex seedGraph N g₁ q₁ r₁ = g₂ →
        edgeVertex seedGraph N g₂ q₂ r₂ = g₀ →
        a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂ = 1) ∧
      ∃ (g : NegativeLevel seedGraph N) (p : Walk seedGraph N g g), p.eval a ≠ 1 := by
  let : LinearOrder SeedCell := LinearOrder.lift' (Fintype.equivFin SeedCell)
    (Fintype.equivFin SeedCell).injective
  obtain ⟨Q,hQ⟩ := exists_generalPosition SeedConnection.connection
  have hf : FlatConnection seedGraph SeedConnection.connection :=
    fun _ _ _ hab hbc hac => SeedConnection.connection_flat hab hbc hac
  obtain ⟨M,hM⟩ := edgeLabel_uniform seedGraph SeedConnection.clique_card_le_three
    SeedConnection.connection Q hQ hε
  let D := Fintype.card SeedCell + 1
  let N := max M (8 * D + 2)
  have hMN : M ≤ N := le_max_left _ _
  have hNbound : 8 * D + 2 ≤ N := le_max_right _ _
  have hN : 1 < N := by omega
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsize : 8 / (N : ℝ) < 1 / (Fintype.card SeedCell + 1 : ℝ) := by
    have hBN : (8 : ℝ) * D + 2 ≤ N := by exact_mod_cast hNbound
    have hDcast : (D : ℝ) = (Fintype.card SeedCell : ℝ) + 1 := by simp [D]
    rw [← hDcast]
    apply (div_lt_div_iff₀ hNr hD).mpr
    nlinarith
  let a := edgeLabel seedGraph SeedConnection.clique_card_le_three
    SeedConnection.connection Q N hN
  refine ⟨N,hN,a,?_,?_,?_,?_⟩
  · exact edgeLabel_reverse seedGraph SeedConnection.clique_card_le_three
      SeedConnection.connection Q hf hQ N hN
  · exact hM N hMN hN
  · exact edgeLabel_triangle seedGraph SeedConnection.clique_card_le_three
      SeedConnection.connection Q hf hQ N hN hsize
  · obtain ⟨p,hp⟩ := exists_nontrivial_level_walk seedGraph SeedConnection.clique_card_le_three
      SeedConnection.connection Q hf hQ N hN seedWalk seedWalk_product_ne
    refine ⟨_,p,?_⟩
    rwa [walkProduct_eq_eval] at hp

end SourceTransport
end EilenbergGanea



end

end OAI
end

section
-- module Solutions.OAIEG.LevelBasis
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea.LevelBasis
variable {V : Type} [LinearOrder V] (L : SimpleGraph V)

/-- The actual oriented crossing-square edges generate precisely the height kernel. -/
theorem generator_surjective (hconn : L.Preconnected) (root : V) :
    Function.Surjective (FreeGroup.lift (generator L (height L) (artinGenerator L) root (height_generator L))) := by
  let f := FreeGroup.lift (generator L (height L) (artinGenerator L) root (height_generator L))
  let F := (height L).ker.subtype.comp f
  have hgen : edgeGenerated L ≤ F.range := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨a,b,hadj,rfl⟩
    have hab : a ≠ b := L.ne_of_adj hadj
    rcases lt_or_gt_of_ne hab with hab | hab
    · refine ⟨(FreeGroup.of (pairShape L a b hab hadj))⁻¹,?_⟩
      change (f ((FreeGroup.of (pairShape L a b hab hadj))⁻¹)).val = _
      simp only [f,map_inv,FreeGroup.lift_apply_of,Subgroup.coe_inv,generator_pair,mul_inv_rev,inv_inv]
      exact (adjacent_generators_commute L hadj).inv_right.eq.symm
    · refine ⟨FreeGroup.of (pairShape L b a hab hadj.symm),?_⟩
      change (f (FreeGroup.of (pairShape L b a hab hadj.symm))).val = _
      simp only [f,FreeGroup.lift_apply_of,generator_pair]
      exact (adjacent_generators_commute L hadj).inv_right.eq.symm
  intro g
  have he : g.val ∈ edgeGenerated L := by rw [edgeGenerated_eq_height_kernel L hconn root]; exact g.property
  obtain ⟨w,hw⟩ := hgen he
  exact ⟨w,Subtype.ext hw⟩

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration
variable {V : Type} [LinearOrder V] [Fintype V] [Nonempty V] (L : SimpleGraph V)

/-- The exactness input to the level slicing is the actual RAAG cube-chain
contraction, not an assumption about a classifying space. -/
theorem artin_total_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) V) (hc : c ∈ total (G := ArtinGroup L) L k)
    (hz : boundary (artinGenerator L) c = 0) :
    ∃ b ∈ total (G := ArtinGroup L) L (k+1), boundary (artinGenerator L) b = c := by
  have he : ∀ n, total (G := ArtinGroup L) L n = TraceWords.CubeDescents.positiveChains L n := by
    intro n
    simp only [total,TraceWords.CubeDescents.positiveChains,SimplicialChains.Valid,and_assoc]
  rw [he] at hc ⊢
  exact TraceWords.CubeDescents.positive_cycle_bounds L hk c hc hz

end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

include comm in
theorem edge_values_compose (a b c : A) (h : SimplicialChains.Valid L [a,b,c]) :
    ((v a)⁻¹ * v b) * ((v b)⁻¹ * v c) = (v a)⁻¹ * v c ∧
    ((v b)⁻¹ * v c) * ((v a)⁻¹ * v b) = (v a)⁻¹ * v c := by
  have he := valid_triangle_edges L h
  have ha : L.Adj a b := by simpa [SimplicialChains.Valid] using he.1.2
  have hb : L.Adj a c := by simpa [SimplicialChains.Valid] using he.2.1.2
  have hc : L.Adj b c := by simpa [SimplicialChains.Valid] using he.2.2.2
  constructor
  · group
  · calc
      ((v b)⁻¹ * v c) * ((v a)⁻¹ * v b) = (v a)⁻¹ * ((v b)⁻¹ * v c) * v b := by
        rw [← mul_assoc,
          ((comm a b ha).inv_left.inv_right.mul_right (comm a c hb).inv_left).symm.eq]
      _ = (v a)⁻¹ * v c := by
        rw [mul_assoc,mul_assoc,← (comm b c hc).eq,inv_mul_cancel_left]

include comm in
theorem triangle_words_trivial (a b c : A) (h : SimplicialChains.Valid L [a,b,c]) :
    let e := valid_triangle_edges L h
    let ab := edgeShape L a b e.1
    let ac := edgeShape L a c e.2.1
    let bc := edgeShape L b c e.2.2
    wordValue (generator L φ v root hv) (lowerTriangleWord L ab ac bc) = 1 ∧
      wordValue (generator L φ v root hv) (upperTriangleWord L ab ac bc) = 1 := by
  dsimp only
  have he := edge_values_compose L v comm a b c h
  constructor <;> apply Subtype.ext
  · simp only [lowerTriangleWord,map_mul,map_inv,wordValue,FreeGroup.lift_apply_of,
      Subgroup.coe_mul,Subgroup.coe_inv,generator_edgeShape,OneMemClass.coe_one]
    group
  · simp only [upperTriangleWord,map_mul,map_inv,wordValue,FreeGroup.lift_apply_of,
      Subgroup.coe_mul,Subgroup.coe_inv,generator_edgeShape,OneMemClass.coe_one]
    rw [he.2,mul_inv_cancel,mul_one,mul_inv_cancel]

include hv in
theorem triangle_boundary_low (g : φ.ker) (a b c : A)
    (h : SimplicialChains.Valid L [a,b,c]) :
    let e := valid_triangle_edges L h
    let ab := edgeShape L a b e.1
    let ac := edgeShape L a c e.2.1
    let bc := edgeShape L b c e.2.2
    triangleBoundary L φ v root hv
        (Finsupp.single (g,triangleShape L a b c h (-1) (Or.inl rfl)) 1) =
      Finsupp.single (g,ac) 1 - Finsupp.single (g,ab) 1 -
        Finsupp.single (g * generator L φ v root hv ab,bc) 1 := by
  dsimp only
  apply includeBasis_injective L φ v root hv 2
  rw [triangleBoundary_inclusion L φ v root hv]
  simp only [map_sub,includeBasis_single,basisIndex,triangleShape,edgeShape,
    List.headD_cons,zpow_neg_one,Subgroup.coe_mul,generator,List.tail_cons]
  simp only [boundary_single,one_smul,boundaryTerm_cons,boundaryTerm_nil,map_zero,
    sub_zero,map_sub,front_single,crossPart,select,Finsupp.linearCombination_single,
    ht_mul,ht_ker,ht_inv,ht_generator φ v hv,List.length_cons,List.length_nil]
  norm_num
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  abel

include hv comm in
theorem triangle_boundary_high (g : φ.ker) (a b c : A)
    (h : SimplicialChains.Valid L [a,b,c]) :
    let e := valid_triangle_edges L h
    let ab := edgeShape L a b e.1
    let ac := edgeShape L a c e.2.1
    let bc := edgeShape L b c e.2.2
    triangleBoundary L φ v root hv
        (Finsupp.single (g,triangleShape L a b c h (-2) (Or.inr rfl)) 1) =
      Finsupp.single (g * generator L φ v root hv ab,bc) 1 -
        Finsupp.single (g * generator L φ v root hv ab,ac) 1 +
        Finsupp.single (g * generator L φ v root hv ac,ab) 1 := by
  dsimp only
  have eh := valid_triangle_edges L h
  have hab : L.Adj a b := by simpa [SimplicialChains.Valid] using eh.1.2
  have hac : L.Adj a c := by simpa [SimplicialChains.Valid] using eh.2.1.2
  apply includeBasis_injective L φ v root hv 2
  rw [triangleBoundary_inclusion L φ v root hv]
  simp only [map_sub,map_add,includeBasis_single,basisIndex,triangleShape,edgeShape,
    List.headD_cons,Subgroup.coe_mul,generator,List.tail_cons]
  simp only [boundary_single,one_smul,boundaryTerm_cons,boundaryTerm_nil,map_zero,
    sub_zero,map_sub,front_single,crossPart,select,map_sub,Finsupp.linearCombination_single,
    ht_mul,ht_ker,ht_zpow,ht_generator φ v hv,List.length_cons,List.length_nil]
  norm_num
  have hb : (v a)^(-2 : ℤ) * v b = (v a)⁻¹ * v b * (v a)⁻¹ := by
    calc
      (v a)^(-2 : ℤ) * v b = (v a)⁻¹ * ((v a)⁻¹ * v b) := by group
      _ = (v a)⁻¹ * (v b * (v a)⁻¹) := congrArg ((v a)⁻¹ * ·) (comm a b hab).inv_left.eq
      _ = _ := (mul_assoc _ _ _).symm
  have hc : (v a)^(-2 : ℤ) * v c = (v a)⁻¹ * v c * (v a)⁻¹ := by
    calc
      (v a)^(-2 : ℤ) * v c = (v a)⁻¹ * ((v a)⁻¹ * v c) := by group
      _ = (v a)⁻¹ * (v c * (v a)⁻¹) := congrArg ((v a)⁻¹ * ·) (comm a c hac).inv_left.eq
      _ = _ := (mul_assoc _ _ _).symm
  have ha : (v a)^(-2 : ℤ) * v a = (v a)⁻¹ := by group
  simp only [zpow_neg,zpow_ofNat] at ha hb hc
  simp only [mul_assoc] at hb hc
  simp only [mul_assoc,ha,hb,hc,mul_inv_cancel,mul_one]
  abel

section WordChains
variable (w : Shape L 2 → G) (ab ac bc : Shape L 2)
theorem lowerTriangleWord_chain (habc : w ab * w bc = w ac) (g : G) :
    pathChain w (lowerTriangleWord L ab ac bc) g =
      Finsupp.single (g,ac) 1 - Finsupp.single (g,ab) 1 -
        Finsupp.single (g * w ab,bc) 1 := by
  simp only [lowerTriangleWord,pathChain_mul,pathChain_inv,pathChain_of,
    map_mul,map_inv,wordValue,FreeGroup.lift_apply_of]
  rw [← habc]
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  abel

theorem upperTriangleWord_chain (habc : w ab * w bc = w ac)
    (hbac : w bc * w ab = w ac) (g : G) :
    pathChain w (upperTriangleWord L ab ac bc) g =
      Finsupp.single (g * w ab,bc) 1 - Finsupp.single (g * w ab,ac) 1 +
        Finsupp.single (g * w ac,ab) 1 := by
  have hr : wordValue w (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) = 1 := by
    simp only [wordValue,map_mul,map_inv,FreeGroup.lift_apply_of,hbac,mul_inv_cancel]
  rw [upperTriangleWord,pathChain_conjugate w _ _ hr]
  simp only [pathChain_mul,pathChain_inv,pathChain_of,map_mul,wordValue,
    FreeGroup.lift_apply_of]
  rw [hbac]
  simp only [mul_assoc,habc,mul_inv_cancel,mul_one]
  abel
end WordChains

include comm in
theorem triangle_words_chain (g : φ.ker) (a b c : A) (h : SimplicialChains.Valid L [a,b,c]) :
    let e := valid_triangle_edges L h
    let ab := edgeShape L a b e.1
    let ac := edgeShape L a c e.2.1
    let bc := edgeShape L b c e.2.2
    pathChain (generator L φ v root hv) (lowerTriangleWord L ab ac bc) g =
      triangleBoundary L φ v root hv
        (Finsupp.single (g,triangleShape L a b c h (-1) (Or.inl rfl)) 1) ∧
    pathChain (generator L φ v root hv) (upperTriangleWord L ab ac bc) g =
      triangleBoundary L φ v root hv
        (Finsupp.single (g,triangleShape L a b c h (-2) (Or.inr rfl)) 1) := by
  dsimp only
  have he := edge_values_compose L v comm a b c h
  have h₁ : generator L φ v root hv (edgeShape L a b (valid_triangle_edges L h).1) *
      generator L φ v root hv (edgeShape L b c (valid_triangle_edges L h).2.2) =
      generator L φ v root hv (edgeShape L a c (valid_triangle_edges L h).2.1) :=
    Subtype.ext he.1
  have h₂ : generator L φ v root hv (edgeShape L b c (valid_triangle_edges L h).2.2) *
      generator L φ v root hv (edgeShape L a b (valid_triangle_edges L h).1) =
      generator L φ v root hv (edgeShape L a c (valid_triangle_edges L h).2.1) :=
    Subtype.ext he.2
  constructor
  · rw [lowerTriangleWord_chain L _ _ _ _ h₁,triangle_boundary_low L φ v root hv]
  · rw [upperTriangleWord_chain L _ _ _ _ h₁ h₂,
      triangle_boundary_high L φ v root hv comm]

theorem shape_three_form (s : Shape L 3) :
    ∃ (a b c : A) (h : SimplicialChains.Valid L [a,b,c]) (n : ℤ) (hn : n = -1 ∨ n = -2),
      s = triangleShape L a b c h n hn := by
  obtain ⟨a,b,c,hw⟩ := List.length_eq_three.mp s.property.2.1
  have hn : s.val.2 = -1 ∨ s.val.2 = -2 := by
    have h₁ := s.property.2.2.1
    have h₂ := s.property.2.2.2
    norm_num at h₂
    omega
  refine ⟨a,b,c,hw ▸ s.property.1,s.val.2,hn,?_⟩
  exact Subtype.ext (Prod.ext hw rfl)

include comm in
theorem triangleWord_trivial (s : Shape L 3) :
    wordValue (generator L φ v root hv) (triangleWord L s) = 1 := by
  obtain ⟨a,b,c,h,n,hn,rfl⟩ := shape_three_form L s
  rcases hn with rfl | rfl
  · simpa [triangleWord,triangleWordList,triangleShape] using
      (triangle_words_trivial L φ v root hv comm a b c h).1
  · simpa [triangleWord,triangleWordList,triangleShape] using
      (triangle_words_trivial L φ v root hv comm a b c h).2

include comm in
theorem triangleWord_chain (s : Shape L 3) (g : φ.ker) :
    pathChain (generator L φ v root hv) (triangleWord L s) g =
      triangleBoundary L φ v root hv (Finsupp.single (g,s) 1) := by
  obtain ⟨a,b,c,h,n,hn,rfl⟩ := shape_three_form L s
  rcases hn with rfl | rfl
  · simpa [triangleWord,triangleWordList,triangleShape] using
      (triangle_words_chain L φ v root hv comm g a b c h).1
  · simpa [triangleWord,triangleWordList,triangleShape] using
      (triangle_words_chain L φ v root hv comm g a b c h).2

end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

include comm in
theorem triangleBoundary_eq_relatorChainMap :
    triangleBoundary L φ v root hv =
      relatorChainMap (generator L φ v root hv) (triangleWord L) := by
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro n
  simp only [LinearMap.coe_comp,Function.comp_apply,Finsupp.lsingle_apply,
    relatorChainMap,Finsupp.linearCombination_single]
  have he : Finsupp.single p n = n • Finsupp.single p (1 : ℤ) := by simp
  rw [he,map_smul,← triangleWord_chain L φ v root hv comm p.2 p.1]

variable (K : SimplicialChains.Contraction L)
variable (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)

theorem triangleBasis_value (c : φ.ker × Shape L 3 →₀ ℤ) :
    (triangleBasis L φ v root hv comm K exactTotal dim c : φ.ker × Shape L 2 →₀ ℤ) =
      relatorChainMap (generator L φ v root hv) (triangleWord L) c := by
  change triangleBoundary L φ v root hv c = _
  rw [triangleBoundary_eq_relatorChainMap L φ v root hv comm]

end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open LevelTransport
variable {V : Type} [LinearOrder V] (L : SimpleGraph V) (root : V) (N : ℕ)

theorem levelEquiv_edge (g : (height L).ker) (q r : V)
    (h : SimplicialChains.Valid L [q,r]) :
    levelEquiv L root N
        (g * generator L (height L) (artinGenerator L) root (height_generator L) (edgeShape L q r h)) =
      edgeVertex L N (levelEquiv L root N g) r q := by
  have ha : L.Adj q r := by simpa [SimplicialChains.Valid] using h.2
  apply Subtype.ext
  simp only [levelEquiv,Equiv.coe_fn_mk,Subgroup.coe_mul,generator_edgeShape,edgeVertex]
  rw [mul_assoc, (adjacent_generators_commute L ha).inv_left.eq]
  group

theorem levelEquiv_edge_inv (g : (height L).ker) (q r : V)
    (h : SimplicialChains.Valid L [q,r]) :
    levelEquiv L root N
        (g * (generator L (height L) (artinGenerator L) root (height_generator L) (edgeShape L q r h))⁻¹) =
      edgeVertex L N (levelEquiv L root N g) q r := by
  have he := levelEquiv_edge L root N
    (g * (generator L (height L) (artinGenerator L) root (height_generator L) (edgeShape L q r h))⁻¹)
    q r h
  simp only [inv_mul_cancel_right] at he
  simpa only [edgeVertex_reverse] using congrArg (fun x => edgeVertex L N x q r) he.symm

variable (a : NegativeLevel L N → V → V → SU2)
variable (rev : ∀ g q r, a (edgeVertex L N g q r) r q = (a g q r)⁻¹)
include rev in
theorem basedLabel_inv_edge (g : (height L).ker) (q r : V)
    (h : SimplicialChains.Valid L [q,r]) :
    (basedLabel L root N a
      (g * (generator L (height L) (artinGenerator L) root (height_generator L) (edgeShape L q r h))⁻¹)
      (edgeShape L q r h))⁻¹ = a (levelEquiv L root N g) q r := by
  rw [basedLabel_edge,levelEquiv_edge_inv,rev,inv_inv]

theorem orientedWord_value (q r : V) (h : L.Adj q r) :
    (wordValue (generator L (height L) (artinGenerator L) root (height_generator L))
      (orientedWord L q r h) : ArtinGroup L) =
        artinGenerator L q * (artinGenerator L r)⁻¹ := by
  unfold orientedWord
  split_ifs
  · simp only [map_inv,wordValue,FreeGroup.lift_apply_of,Subgroup.coe_inv,generator_edgeShape,
      mul_inv_rev,inv_inv]
    exact (adjacent_generators_commute L h).inv_right.symm.eq
  · simp only [wordValue,FreeGroup.lift_apply_of,generator_edgeShape]
    exact (adjacent_generators_commute L h).inv_right.symm.eq

theorem levelEquiv_orientedWord (g : (height L).ker) (q r : V) (h : L.Adj q r) :
    levelEquiv L root N
      (g * wordValue (generator L (height L) (artinGenerator L) root (height_generator L))
        (orientedWord L q r h)) = edgeVertex L N (levelEquiv L root N g) q r := by
  apply Subtype.ext
  simp only [levelEquiv,Equiv.coe_fn_mk,Subgroup.coe_mul,orientedWord_value,edgeVertex,mul_assoc]

include rev in
theorem orientedWord_product (g : (height L).ker) (q r : V) (h : L.Adj q r) :
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a) (orientedWord L q r h) g = a (levelEquiv L root N g) q r := by
  unfold orientedWord
  split_ifs
  · simp only [pathProduct_inv,pathProduct_of,wordValue,FreeGroup.lift_apply_of]
    exact basedLabel_inv_edge L root N a rev g q r _
  · exact pathProduct_of _ _ _ _


include rev in
theorem inverse_edgeWord_product (g : (height L).ker) (q r : V)
    (h : SimplicialChains.Valid L [q,r]) :
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a) (FreeGroup.of (edgeShape L q r h))⁻¹ g =
      a (levelEquiv L root N g) q r := by
  simp only [pathProduct_inv,pathProduct_of,wordValue,FreeGroup.lift_apply_of]
  exact basedLabel_inv_edge L root N a rev g q r h

variable (tri : ∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
    edgeVertex L N g₀ q₀ r₀ = g₁ → edgeVertex L N g₁ q₁ r₁ = g₂ →
      edgeVertex L N g₂ q₂ r₂ = g₀ → a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂ = 1)

include rev tri in
theorem lowerTriangleWord_product (g : (height L).ker) (q r s : V)
    (h : SimplicialChains.Valid L [q,r,s]) :
    let e := valid_triangle_edges L h
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a)
      (lowerTriangleWord L (edgeShape L q r e.1) (edgeShape L q s e.2.1)
        (edgeShape L r s e.2.2)) g = 1 := by
  let gen := generator L (height L) (artinGenerator L) root (height_generator L)
  let e := valid_triangle_edges L h
  let ab := edgeShape L q r e.1
  let ac := edgeShape L q s e.2.1
  let bc := edgeShape L r s e.2.2
  have he : gen ab * gen bc = gen ac :=
    Subtype.ext (edge_values_compose L (artinGenerator L)
      (fun _ _ hh => adjacent_generators_commute L hh) q r s h).1
  have hc : gen ac * (gen bc)⁻¹ = gen ab := by rw [← he]; group
  have hc' : g * gen ac * (gen bc)⁻¹ = g * gen ab := by rw [mul_assoc,hc]
  have ha : g * gen ab * (gen ab)⁻¹ = g := by group
  have T := tri (levelEquiv L root N g) (levelEquiv L root N (g * gen ac))
    (levelEquiv L root N (g * gen ab)) s q r s q r
    (levelEquiv_edge L root N g q s e.2.1).symm
    (by rw [← levelEquiv_edge_inv L root N (g * gen ac) r s e.2.2]; exact congrArg _ hc')
    (by rw [← levelEquiv_edge_inv L root N (g * gen ab) q r e.1]; exact congrArg _ ha)
  change pathProduct gen (basedLabel L root N a) (lowerTriangleWord L ab ac bc) g = 1
  simp only [lowerTriangleWord,pathProduct_mul,pathProduct_of,map_mul,map_inv,
    wordValue,FreeGroup.lift_apply_of]
  rw [hc]
  rw [inverse_edgeWord_product L root N a rev _ r s e.2.2,
    inverse_edgeWord_product L root N a rev _ q r e.1]
  exact T

include rev tri in
theorem upperInnerWord_product (g : (height L).ker) (q r s : V)
    (h : SimplicialChains.Valid L [q,r,s]) :
    let e := valid_triangle_edges L h
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a)
      (FreeGroup.of (edgeShape L r s e.2.2) * FreeGroup.of (edgeShape L q r e.1) *
        (FreeGroup.of (edgeShape L q s e.2.1))⁻¹) g = 1 := by
  let gen := generator L (height L) (artinGenerator L) root (height_generator L)
  let e := valid_triangle_edges L h
  let ab := edgeShape L q r e.1
  let ac := edgeShape L q s e.2.1
  let bc := edgeShape L r s e.2.2
  have he : gen bc * gen ab = gen ac :=
    Subtype.ext (edge_values_compose L (artinGenerator L)
      (fun _ _ hh => adjacent_generators_commute L hh) q r s h).2
  have hc : g * gen bc * gen ab = g * gen ac := by rw [mul_assoc,he]
  have ha : g * gen ac * (gen ac)⁻¹ = g := by group
  have T := tri (levelEquiv L root N g) (levelEquiv L root N (g * gen bc))
    (levelEquiv L root N (g * gen ac)) s r r q q s
    (levelEquiv_edge L root N g r s e.2.2).symm
    (by rw [← levelEquiv_edge L root N (g * gen bc) q r e.1]; exact congrArg _ hc)
    (by rw [← levelEquiv_edge_inv L root N (g * gen ac) q s e.2.1]; exact congrArg _ ha)
  change pathProduct gen (basedLabel L root N a)
    (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) g = 1
  simp only [pathProduct_mul,pathProduct_of,map_mul,wordValue,FreeGroup.lift_apply_of]
  rw [he,inverse_edgeWord_product L root N a rev _ q s e.2.1]
  exact T

include rev tri in
theorem upperTriangleWord_product (g : (height L).ker) (q r s : V)
    (h : SimplicialChains.Valid L [q,r,s]) :
    let e := valid_triangle_edges L h
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a)
      (upperTriangleWord L (edgeShape L q r e.1) (edgeShape L q s e.2.1)
        (edgeShape L r s e.2.2)) g = 1 := by
  let gen := generator L (height L) (artinGenerator L) root (height_generator L)
  let e := valid_triangle_edges L h
  let ab := edgeShape L q r e.1
  let ac := edgeShape L q s e.2.1
  let bc := edgeShape L r s e.2.2
  have he : gen bc * gen ab = gen ac :=
    Subtype.ext (edge_values_compose L (artinGenerator L)
      (fun _ _ hh => adjacent_generators_commute L hh) q r s h).2
  have hr : wordValue gen (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) = 1 := by
    simp only [map_mul,map_inv,wordValue,FreeGroup.lift_apply_of,he,mul_inv_cancel]
  change pathProduct gen (basedLabel L root N a) (upperTriangleWord L ab ac bc) g = 1
  rw [upperTriangleWord,pathProduct_conjugate_loop gen _ _ _ hr]
  rw [upperInnerWord_product L root N a rev tri _ q r s h]
  group

include rev tri in
theorem triangleWord_product (s : Shape L 3) (g : (height L).ker) :
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a) (triangleWord L s) g = 1 := by
  obtain ⟨q,r,t,h,n,hn,rfl⟩ := shape_three_form L s
  rcases hn with rfl | rfl
  · simpa [triangleWord,triangleWordList,triangleShape] using
      lowerTriangleWord_product L root N a rev tri g q r t h
  · simpa [triangleWord,triangleWordList,triangleShape] using
      upperTriangleWord_product L root N a rev tri g q r t h


variable {L N}

 theorem walkWord_endpoint {g k : NegativeLevel L N} (p : Walk L N g k)
    (x : (height L).ker) (hx : levelEquiv L root N x = g) :
    levelEquiv L root N
      (x * wordValue (generator L (height L) (artinGenerator L) root (height_generator L))
        (walkWord p)) = k := by
  induction p generalizing x with
  | nil g => simpa [walkWord] using hx
  | @cons g k q r h p ih =>
    simp only [walkWord,map_mul,← mul_assoc]
    exact ih _ ((levelEquiv_orientedWord L root N x q r h).trans
      (congrArg (fun t => edgeVertex L N t q r) hx))

include rev in
 theorem walkWord_product {g k : NegativeLevel L N} (p : Walk L N g k)
    (x : (height L).ker) (hx : levelEquiv L root N x = g) :
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a) (walkWord p) x = p.eval a := by
  induction p generalizing x with
  | nil g => simp [walkWord,Walk.eval]
  | @cons g k q r h p ih =>
    rw [walkWord,pathProduct_mul,orientedWord_product L root N a rev x q r h]
    rw [ih _ ((levelEquiv_orientedWord L root N x q r h).trans
      (congrArg (fun t => edgeVertex L N t q r) hx)),hx]
    rfl

include rev in
 theorem nontrivial_word_of_walk {g : NegativeLevel L N} (p : Walk L N g g)
    (hp : p.eval a ≠ 1) :
    ∃ (w : FreeGroup (Shape L 2)) (x : (height L).ker),
      wordValue (generator L (height L) (artinGenerator L) root (height_generator L)) w = 1 ∧
      pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
        (basedLabel L root N a) w x ≠ 1 := by
  let x := (levelEquiv L root N).symm g
  have hx : levelEquiv L root N x = g := (levelEquiv L root N).apply_symm_apply g
  refine ⟨walkWord p,x,?_,?_⟩
  · have he := walkWord_endpoint root p x hx
    have he' := (levelEquiv L root N).injective (he.trans hx.symm)
    exact mul_left_cancel (he'.trans (mul_one x).symm)
  · rwa [walkWord_product root a rev p x hx]

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
open LevelTransport
variable {V : Type} [LinearOrder V] [Fintype V] [Nonempty V] (L : SimpleGraph V)
variable [Group.ResiduallyFinite (height L).ker]
variable (root : V) (hconn : L.Preconnected)
variable (K : SimplicialChains.Contraction L)
variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)

include root hconn K dim in
/-- The source obstruction's algebraic endpoint, with no cardinal bound on
an alleged presentation. Its geometric premise must still be derived from an
ordinary two-dimensional classifying CW space. -/
theorem no_boundary_basis_presentation
    (small : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 < N ∧ ∃ a : NegativeLevel L N → V → V → SU2,
      (∀ g q r, a (edgeVertex L N g q r) r q = (a g q r)⁻¹) ∧
      (∀ g q r, dist (a g q r) 1 < ε) ∧
      (∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
        edgeVertex L N g₀ q₀ r₀ = g₁ →
        edgeVertex L N g₁ q₁ r₁ = g₂ →
        edgeVertex L N g₂ q₂ r₂ = g₀ →
        a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂ = 1) ∧
      ∃ (g : NegativeLevel L N) (p : Walk L N g g), p.eval a ≠ 1)
    {A R : Type*} (a₀ : A → (height L).ker)
    (ha₀ : Function.Surjective (wordValue a₀))
    (r₀ : R → FreeGroup A) (hr₀ : ∀ i, wordValue a₀ (r₀ i) = 1)
    (hp₀ : (wordValue a₀).ker = Subgroup.normalClosure (Set.range r₀))
    (E : BasedChains (height L).ker R ≃ₗ[ℤ] cycles a₀)
    (hE : ∀ c, (E c : BasedChains (height L).ker A) = relatorChainMap a₀ r₀ c) : False := by
  let gen := generator L (height L) (artinGenerator L) root (height_generator L)
  let comm := fun q r h => @adjacent_generators_commute V L q r h
  let B := triangleBasis L (height L) (artinGenerator L) root (height_generator L)
    comm K (artin_total_cycle_bounds L) dim
  obtain ⟨η,hη,hηa⟩ := boundary_basis_small_transport gen
    (generator_surjective L hconn root) (triangleWord L)
    (triangleWord_trivial L (height L) (artinGenerator L) root (height_generator L) comm)
    B (triangleBasis_value L (height L) (artinGenerator L) root (height_generator L)
      comm K (artin_total_cycle_bounds L) dim) a₀ ha₀ r₀ hr₀ hp₀ E hE
  obtain ⟨N,_,a,ha,hb,ht,g,p,hp⟩ := small η hη
  obtain ⟨w,x,hw,hx⟩ := nontrivial_word_of_walk root a ha p hp
  apply hx
  exact hηa (basedLabel L root N a)
    (fun x s => by
      simpa only [basedLabel,Subtype.dist_eq,dist_eq_norm,OneMemClass.coe_one] using
        hb (levelEquiv L root N x) (s.val.1.tail.headD root) (s.val.1.headD root))
    (triangleWord_product L root N a ha ht) w hw x

end EilenbergGanea.LevelBasis


end

end OAI
end

section
-- module Solutions.OAIEG.Dimension
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea

attribute [local instance] OAI.EilenbergGanea.instLinearOrderSeedCell_1
theorem source_valid_length_le (w : List SeedCell) (hw : SimplicialChains.Valid seedGraph w) :
    w.length ≤ 3 := by
  simpa only [List.length_map] using
    SeedChainCertificate.valid_length_le (w.map SeedEncoding.cellEquiv) (source_valid_to_index w hw)

/-- The exact remaining geometric interface is not limited to finite or
countable presentations. This endpoint excludes any ordinary presentation
whose actual integral equivariant cellular boundaries freely span cycles. -/
theorem source_no_boundary_basis_of_contraction
    (K : SimplicialChains.Contraction SeedChainCertificate.graph)
    {A R : Type*} (a₀ : A → SourceGroup)
    (ha₀ : Function.Surjective (wordValue a₀))
    (r₀ : R → FreeGroup A) (hr₀ : ∀ i, wordValue a₀ (r₀ i) = 1)
    (hp₀ : (wordValue a₀).ker = Subgroup.normalClosure (Set.range r₀))
    (E : BasedChains SourceGroup R ≃ₗ[ℤ] cycles a₀)
    (hE : ∀ c, (E c : BasedChains SourceGroup A) = relatorChainMap a₀ r₀ c) : False := by
  let : Group.ResiduallyFinite SourceGroup := source_residuallyFinite
  exact LevelBasis.no_boundary_basis_presentation seedGraph seedBase seed_connected.preconnected
    (sourceLinkContraction K) source_valid_length_le SourceTransport.source_small_labels
    a₀ ha₀ r₀ hr₀ hp₀ E hE

end EilenbergGanea



namespace EilenbergGanea

/-- No arbitrary-alphabet genuine presentation has its relators as an integral
basis of Cayley cycles.  -/
theorem source_no_boundary_basis
    {A R : Type*} (a₀ : A → SourceGroup)
    (ha₀ : Function.Surjective (wordValue a₀))
    (r₀ : R → FreeGroup A) (hr₀ : ∀ i, wordValue a₀ (r₀ i) = 1)
    (hp₀ : (wordValue a₀).ker = Subgroup.normalClosure (Set.range r₀))
    (E : BasedChains SourceGroup R ≃ₗ[ℤ] cycles a₀)
    (hE : ∀ c, (E c : BasedChains SourceGroup A) = relatorChainMap a₀ r₀ c) : False :=
  source_no_boundary_basis_of_contraction SeedChainCertificate.contraction
    a₀ ha₀ r₀ hr₀ hp₀ E hE

end EilenbergGanea



end

end OAI
end

section
-- module Solutions.OAIEG.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea
universe u

/-- Exclusion is for arbitrary ordinary2-dimensional classifying CW spaces,
not merely finite presentations or cell complexes with finitely many orbits. -/
theorem source_no_classifyingSpace_two_oai : ¬ HasClassifyingSpace.{u} SourceGroup 2 := by
  rintro ⟨X,tX,hTX,cX,hd,hpc,x,⟨χ⟩,E,tE,hcon,p,cov,hs⟩
  let : TopologicalSpace X := tX
  let : T2Space X := hTX
  let : Topology.CWComplex (Set.univ : Set X) := cX
  let : PathConnectedSpace X := hpc
  let : TopologicalSpace E := tE
  let : ContractibleSpace E := hcon
  obtain ⟨A,a,ha,r,hr,hp,B,hB⟩ := CWPresentation.ordinary_boundary_basis cov hd hs x χ
  exact source_no_boundary_basis a ha r hr hp B hB

end EilenbergGanea


end

end OAI
end

theorem solution.{u} : type_of% @OAI.EilenbergGanea.source_no_classifyingSpace_two_oai.{u} := @OAI.EilenbergGanea.source_no_classifyingSpace_two_oai.{u}
