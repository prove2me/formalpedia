-- Prove2me | solution 1 for OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:30:45.832271+00:00
-- url     : https://prove2.me/submissions/bb569beb-719a-4798-a64b-70b8546929db

import Mathlib
import Definitions.Def_CoboundaryExpanders
import Definitions.Def_OAIQ3Cb002

set_option allowUnsafeReducibility true in
attribute [local reducible] _root_.OAI.CoboundaryExpanders.Complex.Face
section
-- module Solutions.OAIQ3_Cob.Coboundary_Cones
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Quantitative chain cones, face-model transport, relabeling, and exactness under retractions.
-/

section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma rawCone_supported (a : V) (P Q : Set (Finset V))
    (h : ∀ s ∈ P, a ∉ s → insert a s ∈ Q)
    (c : Raw V) (hc : c ∈ supported P) : rawCone a c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs r
  rw [rawCone_single]
  split_ifs with ha
  · exact Submodule.zero_mem _
  · exact single_mem_supported (h s hs ha) r

lemma rawCone_graded (a : V) (P Q : Set (Finset V)) (n : ℕ)
    (h : ∀ s ∈ P, a ∉ s → insert a s ∈ Q)
    (c : Raw V) (hc : c ∈ supported (graded P n)) :
    rawCone a c ∈ supported (graded Q (n+1)) := by
  apply rawCone_supported a (graded P n) (graded Q (n+1)) _ c hc
  intro s hs ha
  exact ⟨h s hs.1 ha, by rw [Finset.card_insert_of_notMem ha, hs.2]⟩

lemma carrierFill_eq (apex : Finset V → V) (s : Finset V) :
    carrierFill apex s = rawCone (apex s)
      (Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v)) := by
  rw [carrierFill]
  congr 2
  exact Finset.sum_coe_sort s (fun v => carrierFill apex (s.erase v))

lemma boundary_carrierFill (apex : Finset V → V) (s : Finset V) :
    rawBoundary (carrierFill apex s) =
      Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hdd := LinearMap.congr_fun (rawBoundary_squared (V := V)) (Finsupp.single s 1)
    have hz := congrArg (carrierMap apex) hdd
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, rawBoundary_single,
      map_sum, carrierMap_single, one_smul, map_zero] at hz
    have he : rawBoundary (∑ v ∈ s, carrierFill apex (s.erase v)) = rawBoundary (Finsupp.single s 1) := by
      rw [map_sum]
      trans ∑ v ∈ s, (Finsupp.single (s.erase v) 1 + ∑ w ∈ s.erase v,
          carrierFill apex ((s.erase v).erase w))
      · apply Finset.sum_congr rfl
        intro v hv
        exact ih (s.erase v) (Finset.erase_ssubset hv)
      · rw [Finset.sum_add_distrib, hz, add_zero, rawBoundary_single]
    have hcycle : rawBoundary (Finsupp.single s 1 + ∑ v ∈ s,
        carrierFill apex (s.erase v)) = 0 := by
      rw [map_add, he, twice]
    rw [carrierFill_eq]
    have h := LinearMap.congr_fun (raw_contraction (apex s))
      (Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v))
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hcycle, map_zero, add_zero] using h

lemma carrierMap_contraction (apex : Finset V → V) :
    rawBoundary.comp (carrierMap apex) + (carrierMap apex).comp rawBoundary = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, carrierMap_single,
    map_smul, boundary_carrierFill, rawBoundary_single, map_sum, LinearMap.id_apply]
  rw [smul_add, Finset.smul_sum]
  have h : (∑ v ∈ s, a • carrierFill apex (s.erase v)) +
      (∑ v ∈ s, a • carrierFill apex (s.erase v)) = 0 := twice _
  rw [add_assoc, h, add_zero]
  simp

lemma carrierFill_size (apex : Finset V → V) (s : Finset V) :
    size (carrierFill apex s) ≤ carrierBound s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rw [carrierFill_eq]
    calc
      size (rawCone (apex s) _) ≤ size (Finsupp.single s 1 +
          ∑ v ∈ s, carrierFill apex (s.erase v)) := size_rawCone_le _ _
      _ ≤ 1 + ∑ v ∈ s, size (carrierFill apex (s.erase v)) :=
        (size_add_le _ _).trans (Nat.add_le_add (size_single_le _ _) (size_sum_le _ _))
      _ ≤ 1 + s.card * carrierBound (s.card-1) := by
        apply Nat.add_le_add_left
        calc
          (∑ v ∈ s, size (carrierFill apex (s.erase v))) ≤
              ∑ _v ∈ s, carrierBound (s.card-1) := by
            apply Finset.sum_le_sum
            intro v hv
            simpa only [Finset.card_erase_of_mem hv] using ih (s.erase v) (Finset.erase_ssubset hv)
          _ = _ := by simp
      _ = carrierBound s.card := by
        cases he : s.card with
        | zero => simp [carrierBound]
        | succ n => simp [carrierBound]

lemma carrierFill_supported (X : CoboundaryExpanders.InfiniteChains.Complex V) (C : Finset V → Set (Finset V))
    (apex : Finset V → V)
    (hself : ∀ s ∈ X.faces, s ∈ C s)
    (hmono : ∀ s ∈ X.faces, ∀ t ⊆ s, C t ⊆ C s)
    (hcone : ∀ s ∈ X.faces, ∀ t ∈ C s, insert (apex s) t ∈ C s)
    (s : Finset V) (hs : s ∈ X.faces) :
    carrierFill apex s ∈ supported (graded (C s) (s.card+1)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rw [carrierFill_eq]
    apply rawCone_graded (apex s) (C s) (C s) s.card
      (fun t ht _ => hcone s hs t ht)
    apply Submodule.add_mem
    · exact single_mem_supported (P := graded (C s) s.card) ⟨hself s hs, rfl⟩ _
    · apply Submodule.sum_mem
      intro v hv
      have hi := ih (s.erase v) (Finset.erase_ssubset hv)
        (X.downward hs (Finset.erase_subset _ _))
      apply supported_mono (P := graded (C (s.erase v)) ((s.erase v).card+1))
        (Q := graded (C s) s.card) ?_ hi
      intro t ht
      refine ⟨hmono s hs _ (Finset.erase_subset _ _) ht.1, ?_⟩
      have htcard := ht.2
      rw [Finset.card_erase_of_mem hv] at htcard
      have hpos := Finset.card_pos.mpr ⟨v, hv⟩
      omega

lemma cone_link_without (v : V) (c : Raw V) :
    rawCone v (link v c) + without v c = c := by
  have h : (rawCone v).comp (link v) + without v = LinearMap.id := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
      link_single, without_single, LinearMap.id_apply]
    by_cases hv : v ∈ s
    · simp [hv, Finset.insert_erase hv]
    · simp [hv]
  exact LinearMap.congr_fun h c

lemma link_boundary (v : V) :
    (link v).comp rawBoundary = rawBoundary.comp (link v) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rawBoundary_single, map_sum,
    link_single]
  by_cases hv : v ∈ s
  · rw [ite_eq_left hv, rawBoundary_single]
    rw [← Finset.sum_erase_add _ _ hv]
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro w hw
    have hwv := (Finset.mem_erase.mp hw).1
    rw [ite_eq_left ⟨Ne.symm hwv, hv⟩, Finset.erase_right_comm]
  · rw [ite_eq_right hv, map_zero]
    apply Finset.sum_eq_zero
    intro w hw
    exact ite_eq_right (fun h => hv (Finset.mem_of_mem_erase h))

lemma link_cycle (v : V) (c : Raw V) (hc : rawBoundary c = 0) :
    rawBoundary (link v c) = 0 := by
  have h := LinearMap.congr_fun (link_boundary v) c
  simpa [hc] using h.symm

lemma link_supported (v : V) (P Q : Set (Finset V))
    (h : ∀ s ∈ P, v ∈ s → s.erase v ∈ Q)
    (c : Raw V) (hc : c ∈ supported P) : link v c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs a
  rw [link_single]
  split_ifs with hv
  · exact single_mem_supported (h s hs hv) a
  · exact Submodule.zero_mem _

lemma link_graded (v : V) (P Q : Set (Finset V)) (n : ℕ)
    (h : ∀ s ∈ P, v ∈ s → s.erase v ∈ Q)
    (c : Raw V) (hc : c ∈ supported (graded P (n+1))) :
    link v c ∈ supported (graded Q n) := by
  apply link_supported v (graded P (n+1)) (graded Q n) _ c hc
  intro s hs hv
  exact ⟨h s hs.1 hv, by rw [Finset.card_erase_of_mem hv, hs.2]; omega⟩

lemma without_supported (v : V) (P : Set (Finset V))
    (c : Raw V) (hc : c ∈ supported P) :
    without v c ∈ supported {s | s ∈ P ∧ v ∉ s} := by
  apply map_supported _ P _ _ c hc
  intro s hs a
  rw [without_single]
  split_ifs with hv
  · exact Submodule.zero_mem _
  · exact single_mem_supported (P := {s | s ∈ P ∧ v ∉ s}) ⟨hs, hv⟩ a

lemma link_size (v : V) (c : Raw V) : size (link v c) ≤ size c := by
  have h := size_map_le (link v) Set.univ 1 (fun s _ => by
    rw [link_single]
    split_ifs
    · exact size_single_le _ _
    · simp) c (by rw [mem_supported]; simp)
  simpa using h

lemma without_size (v : V) (c : Raw V) : size (without v c) ≤ size c := by
  have h := size_map_le (without v) Set.univ 1 (fun s _ => by
    rw [without_single]
    split_ifs
    · simp
    · exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

lemma elimination_identity (v : V) (c b : Raw V) (hb : rawBoundary b = link v c) :
    rawBoundary (rawCone v b) + (without v c + b) = c := by
  have h := LinearMap.congr_fun (raw_contraction v) b
  have he : rawBoundary (rawCone v b) + rawCone v (link v c) = b := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hb] using h
  have he' : rawBoundary (rawCone v b) = b + rawCone v (link v c) := by
    calc
      rawBoundary (rawCone v b) = rawBoundary (rawCone v b) +
          (rawCone v (link v c) + rawCone v (link v c)) := by rw [twice, add_zero]
      _ = b + rawCone v (link v c) := by rw [← add_assoc, he]
  rw [he']
  calc
    b + rawCone v (link v c) + (without v c + b) =
        (rawCone v (link v c) + without v c) + (b+b) := by ac_rfl
    _ = c := by rw [twice, add_zero, cone_link_without]

lemma elimination_cycle (v : V) (c b : Raw V) (hc : rawBoundary c = 0)
    (hb : rawBoundary b = link v c) : rawBoundary (without v c + b) = 0 := by
  have he := congrArg rawBoundary (elimination_identity v c b hb)
  have hdd := LinearMap.congr_fun (rawBoundary_squared (V := V)) (rawCone v b)
  have hdd' : rawBoundary (rawBoundary (rawCone v b)) = 0 := hdd
  simpa only [map_add, hdd', zero_add, hc] using he

namespace BoundedCone
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)

lemma fills (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) (hz : rawBoundary c = 0) :
    rawBoundary (H.hom c) = c := by
  simpa only [hz, map_zero, add_zero] using H.contraction_apply r hr c hc

end BoundedCone

lemma mem_vertices (c : Raw V) (s : Finset V) (hs : c s ≠ 0) (v : V) (hv : v ∈ s) :
    v ∈ vertices c := Finset.mem_biUnion.mpr ⟨s, Finsupp.mem_support_iff.mpr hs, hv⟩

lemma vertices_card_le (P : Set (Finset V)) (r : ℕ) (c : Raw V)
    (hc : c ∈ supported (graded P r)) : (vertices c).card ≤ r * size c := by
  calc
    (vertices c).card ≤ ∑ s ∈ c.support, s.card := Finset.card_biUnion_le
    _ = r * size c := by
      rw [Finset.sum_congr rfl (fun s hs =>
        ((mem_supported _ _).mp hc s (Finsupp.mem_support_iff.mp hs)).2)]
      simp [size, Nat.mul_comm]

omit [DecidableEq V] in
lemma allowed_forget (X : CoboundaryExpanders.InfiniteChains.Complex V) (bad : V → Prop) (A : Finset V) (r : ℕ) :
    supported (graded (allowed X bad A).faces r) ≤ supported (graded X.faces r) :=
  supported_mono (fun _ hs => ⟨hs.1.1, hs.2⟩)

lemma removeBad (X : CoboundaryExpanders.InfiniteChains.Complex V) (bad : V → Prop) (r R : ℕ)
    (linkFill : ∀ v, bad v → ∀ c : Raw V,
      c ∈ supported (graded X.faces r) → rawBoundary c = 0 →
      ∃ b : Raw V,
        b ∈ supported (graded {s | s ∈ X.faces ∧
          (∀ w ∈ s, ¬bad w) ∧ insert v s ∈ X.faces} r) ∧
        rawBoundary b = link v c ∧ size b ≤ R * size c)
    (A : Finset V) (hA : ∀ v ∈ A, bad v) (c : Raw V)
    (hc : c ∈ supported (graded (allowed X bad A).faces r)) (hz : rawBoundary c = 0) :
    ∃ e c' : Raw V,
      e ∈ supported (graded X.faces (r+1)) ∧
      c' ∈ supported (graded (allowed X bad ∅).faces r) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c ∧
      size e + size c' ≤ (2*R+2)^A.card * size c := by
  induction A using Finset.induction_on generalizing c with
  | empty =>
    refine ⟨0, c, Submodule.zero_mem _, hc, hz, by simp, ?_⟩
    simp
  | @insert v A hv ih =>
    have hcX := allowed_forget X bad (insert v A) r hc
    obtain ⟨b, hb, hdb, hsize⟩ := linkFill v (hA v (Finset.mem_insert_self _ _)) c hcX hz
    let P : Set (Finset V) := {s | s ∈ X.faces ∧ (∀ w ∈ s, ¬ bad w) ∧ insert v s ∈ X.faces}
    have hbP : b ∈ supported (graded P r) := hb
    have hbA : b ∈ supported (graded (allowed X bad A).faces r) := by
      apply supported_mono (P := graded P r) (Q := graded (allowed X bad A).faces r) ?_ hbP
      intro s hs
      exact ⟨⟨hs.1.1, fun w hw hbad => False.elim (hs.1.2.1 w hw hbad)⟩, hs.2⟩
    have hwA : without v c ∈ supported (graded (allowed X bad A).faces r) := by
      have hw := without_supported v (graded (allowed X bad (insert v A)).faces r) c hc
      apply supported_mono (P := {s | s ∈ graded (allowed X bad (insert v A)).faces r ∧ v ∉ s})
        (Q := graded (allowed X bad A).faces r) ?_ hw
      intro s hs
      refine ⟨⟨hs.1.1.1, ?_⟩, hs.1.2⟩
      intro w hw hbad
      rcases Finset.mem_insert.mp (hs.1.1.2 w hw hbad) with he | he
      · exact False.elim (hs.2 (he ▸ hw))
      · exact he
    have hz' := elimination_cycle v c b hz hdb
    obtain ⟨e, c', he, hc', hz'', hec', hbound⟩ :=
      ih (fun w hw => hA w (Finset.mem_insert_of_mem hw))
        (without v c + b) (Submodule.add_mem _ hwA hbA) hz'
    have hcone : rawCone v b ∈ supported (graded X.faces (r+1)) :=
      rawCone_graded v P X.faces r (fun s hs _ => hs.2.2) b hbP
    refine ⟨rawCone v b + e, c', Submodule.add_mem _ hcone he, hc', hz'', ?_, ?_⟩
    · rw [map_add, add_assoc, hec']
      exact elimination_identity v c b hdb
    · have hnew : size (without v c + b) ≤ (R+1)*size c := by
        have hw := without_size v c
        have hadd := size_add_le (without v c) b
        nlinarith
      have hconesize : size (rawCone v b) ≤ R*size c := (size_rawCone_le _ _).trans hsize
      have hp : 1 ≤ (2*R+2)^A.card := Nat.one_le_pow _ _ (by omega)
      have hh := Nat.mul_le_mul_left ((2*R+2)^A.card) hnew
      have hbnd := size_add_le (rawCone v b) e
      rw [Finset.card_insert_of_notMem hv, pow_succ]
      nlinarith

omit [DecidableEq V] in
lemma relabel_injective (f : V → W) (hf : Function.Injective f) :
    Function.Injective (relabel f) :=
  Finsupp.mapDomain_injective (Finset.image_injective hf)

end CoboundaryExpanders.InfiniteChains.Cone

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

end

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V : Type} [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma vertexEval_boundary {X : CoboundaryExpanders.InfiniteChains.Complex V} (P : V → Prop)
    (hP : ∀ a b, ({a,b}:Finset V) ∈ X.faces → (P a ↔ P b))
    (c : Raw V) (hc : c ∈ supported (graded X.faces 2)) :
    vertexEval P (rawBoundary c) = 0 := by
  have hsingle (s : Finset V) (hs : s ∈ graded X.faces 2) :
      vertexEval P (rawBoundary (Finsupp.single s 1)) = 0 := by
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hs.2
    have hp := hP a b hs.1
    rw [rawBoundary_single,Finset.sum_insert (show a ∉ ({b}:Finset V) by simpa using hab),
      Finset.sum_singleton,map_add]
    have hea : ({a,b}:Finset V).erase a = {b} := by simp [hab]
    have heb : ({a,b}:Finset V).erase b = {a} := by
      rw [Finset.erase_insert_of_ne hab,Finset.erase_singleton]
      rfl
    rw [hea,heb,vertexEval_single,vertexEval_single]
    simp only [one_mul,Finset.sum_singleton]
    by_cases ha : P a
    · have hb := hp.mp ha
      simp only [ite_eq_left ha,ite_eq_left hb]
      exact CharTwo.add_self_eq_zero _
    · have hb : ¬P b := fun h => ha (hp.mpr h)
      simp only [ite_eq_right ha,ite_eq_right hb,zero_add]
  rw [←Finsupp.sum_single c,Finsupp.sum,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have he : Finsupp.single s (c s) = c s • Finsupp.single s (1:k) := by simp
  rw [he,map_smul,map_smul,hsingle s ((mem_supported _ c).mp hc s (Finsupp.mem_support_iff.mp hs)),smul_zero]

theorem BoundedCone.vertexPath {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (hn : 1 ≤ n) (x y : V) (hx : ({x}:Finset V) ∈ X.faces)
    (hy : ({y}:Finset V) ∈ X.faces) : VertexPath X x y := by
  let P : V → Prop := VertexPath X x
  have hP (a b : V) (hab : ({a,b}:Finset V) ∈ X.faces) : P a ↔ P b := by
    constructor
    · intro ha; exact ha.tail hab
    · intro hb; exact hb.tail (by simpa [Finset.pair_comm] using hab)
  let c : Raw V := Finsupp.single {x} 1+Finsupp.single {y} 1
  have hc : c ∈ supported (graded X.faces 1) := by
    dsimp only [c]
    apply Submodule.add_mem
    · exact single_mem_supported (P:=graded X.faces 1) ⟨hx,Finset.card_singleton x⟩ _
    · exact single_mem_supported (P:=graded X.faces 1) ⟨hy,Finset.card_singleton y⟩ _
  have hz : rawBoundary c = 0 := by
    simp only [c,map_add,rawBoundary_single,Finset.sum_singleton,Finset.erase_singleton]
    exact twice _
  have hb := vertexEval_boundary P hP (H.hom c) (H.map_graded 1 hn c hc)
  rw [H.fills 1 hn c hc hz] at hb
  have hpx : P x := Relation.ReflTransGen.refl
  by_contra hpy
  have hpy' : ¬P y := hpy
  simp only [c,map_add,vertexEval_single,Finset.sum_singleton,one_mul,ite_eq_left hpx,ite_eq_right hpy',add_zero] at hb
  exact one_ne_zero hb
end CoboundaryExpanders.InfiniteChains.Cone

end

open scoped Polynomial BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Basic
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Polynomial congruence groups, truncation ideals, and finite nilpotent quotients.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix

namespace CoboundaryExpanders.Construction

variable (p n : ℕ) [Fact p.Prime]

theorem localGroup_card_le (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Nat.card (localGroup p n hn cut) ≤
      Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p)) := by
  exact (Nat.card_le_card_of_injective (localGroupEmbedding p n hn cut)
    (localGroupEmbedding p n hn cut).injective).trans
    (Nat.card_le_card_of_surjective _
      (Matrix.GeneralLinearGroup.map (n := Fin (n + 1))
        (algebraMap (ZMod p) (Frac p))).rangeRestrict_surjective)

theorem reducedLocalMap_surjective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    Function.Surjective (reducedLocalMap p n hn m cut) := by
  rintro ⟨g, h⟩
  obtain ⟨u, hu, e⟩ := h
  exact ⟨⟨u, hu⟩, Subtype.ext e⟩

theorem reducedLocalGroup_card_le (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    Nat.card (reducedLocalGroup p n hn m cut) ≤
      Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p)) := by
  exact (Nat.card_le_card_of_surjective _ (reducedLocalMap_surjective p n hn m cut)).trans
    ((Nat.card_le_card_of_injective _ (uLocalEmbedding p n hn cut).injective).trans
      (localGroup_card_le p n hn cut))

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Cosets
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutVertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Typed coset complexes, their links, face models, and connectedness from generation.
-/

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains InfiniteChains.Cone
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma vertexPath_common (g : G) (i j : I) :
    VertexPath (complex H) (vertex H g i) (vertex H g j) := by
  apply Relation.ReflTransGen.single
  exact ⟨g,{i,j},by simp [face]⟩

lemma vertexPath_symm {x y : Vertex H} (h : VertexPath (complex H) x y) :
    VertexPath (complex H) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
    exact (Relation.ReflTransGen.single (by simpa only [Finset.pair_comm] using hxy)).trans ih

lemma vertexPath_mul (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) (base : I) (x : G) :
    ∀ g, VertexPath (complex H) (vertex H g base) (vertex H (g*x) base) := by
  have hx : x ∈ Subgroup.closure (⋃ i, (H i : Set G)) := by rw [hgen]; trivial
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    intro g
    have he : vertex H g i = vertex H (g*x) i := by
      apply Sigma.mk.inj_iff.mpr
      refine ⟨rfl,heq_of_eq ?_⟩
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simpa using hi))
    have hleft := vertexPath_common H g base i
    have hright := vertexPath_common H (g*x) i base
    rw [←he] at hright
    exact hleft.trans hright
  | one => intro g; simpa only [mul_one,VertexPath] using (Relation.ReflTransGen.refl : VertexPath (complex H) (vertex H g base) _)
  | mul x y hx hy ihx ihy => intro g; simpa only [mul_assoc,VertexPath] using (ihx g).trans (ihy (g*x))
  | inv x hx ih =>
    intro g
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using vertexPath_symm H (ih (g*x⁻¹))

lemma vertexPath_of_generate (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤)
    (base : I) (x y : Vertex H) : VertexPath (complex H) x y := by
  obtain ⟨i,x⟩ := x
  obtain ⟨j,y⟩ := y
  induction x using Quotient.inductionOn with | h g =>
    induction y using Quotient.inductionOn with | h h =>
      change VertexPath (complex H) (vertex H g i) (vertex H h j)
      have hd := vertexPath_mul H hgen base (g⁻¹*h) g
      simp only [←mul_assoc,mul_inv_cancel,one_mul] at hd
      exact (vertexPath_common H g i base).trans (hd.trans (vertexPath_common H h base j))

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Flags
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Complete flags, spherical opposition, unitriangular groups, and the flag-coset model.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.SphericalOpposition
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

variable {N : ℕ}

namespace CompleteFlag
variable [FiniteDimensional K V]

lemma forbidden_rank (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N) :
    finrank K (F.forbidden W) = N-1 := by
  have hd := F.opposed_disjoint_below W hW ⟨N-finrank K W-1, by omega⟩ (by simp)
  have he := Submodule.finrank_sup_add_finrank_inf_eq W
    (F.space ⟨N-finrank K W-1, by omega⟩)
  rw [hd.eq_bot, finrank_bot, F.rank, add_zero] at he
  dsimp only [Fin.val_mk] at he
  change finrank K (W ⊔ F.space ⟨N-finrank K W-1, by omega⟩ : Submodule K V) = N-1
  omega

lemma forbidden_ne_top (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N) : F.forbidden W ≠ ⊤ := by
  intro e
  have he := F.forbidden_rank W hW hlt
  rw [e, finrank_top, F.dimension] at he
  omega

lemma extension_rank (F : CompleteFlag K V N) (W : Submodule K V)
    {v : V} (hv : v ∉ F.forbidden W) :
    finrank K (W ⊔ Submodule.span K {v} : Submodule K V) = finrank K W + 1 := by
  apply Submodule.finrank_sup_span_singleton
  exact fun h => hv ((show W ≤ F.forbidden W from le_sup_left) h)

lemma opposed_extension (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N)
    {v : V} (hv : v ∉ F.forbidden W) :
    F.Opposed (W ⊔ Submodule.span K {v}) := by
  let A := F.space ⟨N-finrank K W-1, by omega⟩
  have hr : finrank K (W ⊔ Submodule.span K {v} : Submodule K V) = finrank K W + 1 :=
    F.extension_rank W hv
  have ht : W ⊔ Submodule.span K {v} ⊔ A = ⊤ := by
    have hb := Submodule.finrank_sup_span_singleton hv
    rw [F.forbidden_rank W hW hlt] at hb
    have he : F.forbidden W ⊔ Submodule.span K {v} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [F.dimension]
      omega
    simpa [forbidden, A, sup_assoc, sup_comm, sup_left_comm] using he
  have hai : (⟨N-finrank K (W ⊔ Submodule.span K {v} : Submodule K V), by omega⟩ : Fin (N+1)) =
      ⟨N-finrank K W-1, by omega⟩ := by
    apply Fin.ext
    dsimp
    omega
  rw [F.opposed_iff_disjoint, hai]
  apply disjoint_iff.mpr
  apply Submodule.finrank_eq_zero.mp
  have he := Submodule.finrank_sup_add_finrank_inf_eq (W ⊔ Submodule.span K {v}) A
  rw [ht, finrank_top, F.dimension, hr, F.rank] at he
  dsimp [A] at he ⊢
  omega

lemma good_extension (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Good W) (hlt : finrank K W + 1 < N)
    {v : V} (hv : v ∉ F.forbidden W) :
    F.Good (W ⊔ Submodule.span K {v}) := by
  refine ⟨?_, ?_, F.opposed_extension W hW.2.2 hW.2.1 hv⟩ <;>
    rw [F.extension_rank W hv] <;> omega

lemma opposed_line (F : CompleteFlag K V N) (hN : 0 < N) {v : V}
    (hv : v ∉ F.space ⟨N-1, by omega⟩) : F.Opposed (Submodule.span K {v}) := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact Submodule.zero_mem _)
  rw [F.opposed_iff_disjoint]
  simpa only [finrank_span_singleton hv0] using (Submodule.disjoint_span_singleton_of_notMem hv).symm

lemma good_line (F : CompleteFlag K V N) (hN : 1 < N) {v : V}
    (hv : v ∉ F.space ⟨N-1, by omega⟩) : F.Good (Submodule.span K {v}) := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact Submodule.zero_mem _)
  refine ⟨?_, ?_, F.opposed_line (by omega) hv⟩ <;>
    rw [finrank_span_singleton hv0] <;> omega

lemma good_lower_map (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (A : Submodule K W) (hA : (F.lower W hW).Good A) :
    F.Good (A.map W.subtype) := by
  refine ⟨?_, ?_, (F.opposed_lower_iff W hW A).mp hA.2.2⟩
  · simpa only [Submodule.finrank_map_subtype_eq] using hA.1
  · rw [Submodule.finrank_map_subtype_eq]
    exact lt_of_lt_of_le hA.2.1 (F.rank_le W)

lemma sup_mem_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hne : s.Nonempty) : s.sup id ∈ s := by
  obtain ⟨W, hW, hmax⟩ := F.face_has_greatest s hs hne
  have he : s.sup id = W := le_antisymm (Finset.sup_le hmax) (Finset.le_sup (f := id) hW)
  exact he ▸ hW

omit [FiniteDimensional K V] in
lemma carrierApex_mono (F : CompleteFlag K V N) (v : V)
    {s t : Finset (Submodule K V)} (hst : s ⊆ t) :
    F.carrierApex v s ≤ F.carrierApex v t := by
  apply sup_le_sup_right
  exact Finset.sup_mono hst

lemma carrierApex_good (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) : F.Good (F.carrierApex v s) := by
  rcases s.eq_empty_or_nonempty with he | he
  · subst s
    simpa [carrierApex] using F.good_line hN hv
  · have hm := F.sup_mem_face s hs.1 he
    exact F.good_extension (s.sup id) (hs.1.1 _ hm) (hs.2 _ hm).1 (hs.2 _ hm).2

omit [FiniteDimensional K V] in
lemma self_mem_carrier (F : CompleteFlag K V N) (v : V) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) : s ∈ F.carrier v s :=
  ⟨hs.1, fun _ hW => (Finset.le_sup (f := id) hW).trans le_sup_left⟩

omit [FiniteDimensional K V] in
lemma carrier_mono (F : CompleteFlag K V N) (v : V) {s t : Finset (Submodule K V)}
    (hst : s ⊆ t) : F.carrier v s ⊆ F.carrier v t :=
  fun _ ha => ⟨ha.1, fun W hW => (ha.2 W hW).trans (F.carrierApex_mono v hst)⟩

lemma carrier_cone (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) (t : Finset (Submodule K V))
    (ht : t ∈ F.carrier v s) : insert (F.carrierApex v s) t ∈ F.carrier v s := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact F.carrierApex_good hN v hv s hs
    · exact ht.1.1 W hW
  · intro W hW U hU hne
    rcases Finset.mem_insert.mp hW with rfl | hW
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact False.elim (hne rfl)
      · exact Or.inr (ht.2 U hU)
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact Or.inl (ht.2 W hW)
      · exact ht.1.2 hW hU hne
  · intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact le_rfl
    · exact ht.2 W hW

lemma good_lower_comap (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (A : Submodule K V) (hA : F.Good A) (hAW : A < W) :
    (F.lower W hW).Good (A.comap W.subtype) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rank_comap_lower W A hAW.le]
    exact hA.1
  · rw [rank_comap_lower W A hAW.le]
    exact Submodule.finrank_strictMono hAW
  · rw [F.opposed_lower_iff W hW, map_comap_lower W A hAW.le]
    exact hA.2.2

lemma lower_face_map (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (s : Finset (Submodule K W))
    (hs : s ∈ (F.lower W hW).complex.faces) :
    s.image (Submodule.map W.subtype) ∈ F.complex.faces ∧
      ∀ A ∈ s.image (Submodule.map W.subtype), A < W := by
  have hinj := Submodule.map_injective_of_injective W.injective_subtype
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact F.good_lower_map W hW B (hs.1 B hB)
  · intro A hA B hB hab
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    exact (hs.2 hA' hB' (fun e => hab (congrArg _ e))).imp Submodule.map_mono Submodule.map_mono
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    refine lt_of_le_of_ne ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      exact y.property
    · intro he
      have hr := congrArg (fun U : Submodule K V => finrank K U) he
      rw [Submodule.finrank_map_subtype_eq] at hr
      exact (ne_of_lt (hs.1 B hB).2.1) hr

lemma lower_face_comap (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hsW : ∀ A ∈ s, A < W) :
    s.image (Submodule.comap W.subtype) ∈ (F.lower W hW).complex.faces := by
  refine ⟨?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact F.good_lower_comap W hW B (hs.1 B hB) (hsW B hB)
  · intro A hA B hB hab
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    exact (hs.2 hA' hB' (fun e => hab (congrArg _ e))).imp Submodule.comap_mono Submodule.comap_mono

omit [FiniteDimensional K V] in
lemma comap_injOn_lower (W : Submodule K V) (s : Finset (Submodule K V))
    (hs : ∀ A ∈ s, A ≤ W) : Set.InjOn (Submodule.comap W.subtype) (s : Set (Submodule K V)) := by
  intro A hA B hB he
  have hm := congrArg (Submodule.map W.subtype) he
  rwa [map_comap_lower W A (hs A hA), map_comap_lower W B (hs B hB)] at hm

lemma hyperplane_link_lower (F : CompleteFlag K V N) (W : Submodule K V)
    (hr : finrank K W = N-1) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hW : W ∈ s) :
    ∀ A ∈ s.erase W, A < W := by
  intro A hA
  obtain ⟨hne, hAs⟩ := Finset.mem_erase.mp hA
  rcases hs.2 hAs hW hne with h | h
  · exact lt_of_le_of_ne h hne
  · have he : W = A := Submodule.eq_of_le_of_finrank_le h (by
      have ha := (hs.1 A hAs).2.1
      omega)
    exact False.elim (hne he.symm)

omit [FiniteDimensional K V] in
lemma insert_greatest_face (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Good W) (s : Finset (Submodule K V)) (hs : s ∈ F.complex.faces)
    (hsW : ∀ A ∈ s, A ≤ W) : insert W s ∈ F.complex.faces := by
  refine ⟨?_, ?_⟩
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hAs
    · exact hW
    · exact hs.1 A hAs
  · intro A hA B hB hab
    rcases Finset.mem_insert.mp hA with heA | hAs
    · subst A
      rcases Finset.mem_insert.mp hB with heB | hBs
      · exact False.elim (hab heB.symm)
      · exact Or.inr (hsW B hBs)
    · rcases Finset.mem_insert.mp hB with heB | hBs
      · subst B
        exact Or.inl (hsW A hAs)
      · exact hs.2 hAs hBs hab

end CompleteFlag

theorem exists_vector_avoiding [Fintype K] [Fintype V] [FiniteDimensional K V]
    {ι : Type} [Fintype ι] (P : ι → Submodule K V)
    (hP : ∀ i, P i ≠ ⊤) (hι : Fintype.card ι < Fintype.card K)
    (hdim : 0 < finrank K V) : ∃ v : V, ∀ i, v ∉ P i := by
  classical
  let bad : Finset V := Finset.univ.biUnion (fun i => (P i : Set V).toFinset)
  have hbound (i : ι) : (P i : Set V).toFinset.card ≤
      Fintype.card K ^ (finrank K V - 1) := by
    rw [Set.toFinset_card]
    change Fintype.card (P i) ≤ _
    rw [Module.card_eq_pow_finrank (K := K)]
    exact Nat.pow_le_pow_right Fintype.card_pos (by have := Submodule.finrank_lt (hP i); omega)
  have hcard : bad.card < Finset.univ.card (α := V) := by
    calc
      bad.card ≤ ∑ i : ι, (P i : Set V).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, Fintype.card K ^ (finrank K V - 1) :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = Fintype.card ι * Fintype.card K ^ (finrank K V - 1) := by simp
      _ < Fintype.card K * Fintype.card K ^ (finrank K V - 1) :=
        Nat.mul_lt_mul_of_pos_right hι (Nat.pow_pos Fintype.card_pos)
      _ = Fintype.card K ^ finrank K V := by
        rw [← pow_succ']
        congr 1
        omega
      _ = Finset.univ.card (α := V) := by rw [Finset.card_univ, Module.card_eq_pow_finrank (K := K) (V := V)]
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨v, fun i hi => hv ?_⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using hi⟩

theorem exists_vector_avoiding_finset [Fintype K] [Fintype V] [FiniteDimensional K V]
    (S : Finset (Submodule K V)) (hS : ∀ P ∈ S, P ≠ ⊤)
    (hcard : S.card < Fintype.card K) (hdim : 0 < finrank K V) :
    ∃ v : V, ∀ P ∈ S, v ∉ P := by
  classical
  obtain ⟨v, hv⟩ := exists_vector_avoiding (fun P : S => P.val)
    (fun P => hS P.val P.property) (by simpa using hcard) hdim
  exact ⟨v, fun P hP => hv ⟨P, hP⟩⟩

theorem exists_common_good_line [Fintype K] [Fintype V] [FiniteDimensional K V]
    {ι : Type} [Fintype ι] [Nonempty ι] (F : ι → CompleteFlag K V N)
    (hN : 1 < N) (hι : Fintype.card ι < Fintype.card K) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, (F i).Good (Submodule.span K {v}) := by
  classical
  let base : ι := Classical.choice inferInstance
  obtain ⟨v, hv⟩ := exists_vector_avoiding
    (fun i => (F i).space ⟨N-1, by omega⟩) (fun i => by
      intro he
      have hr := (F i).rank ⟨N-1, by omega⟩
      rw [he, finrank_top, (F i).dimension] at hr
      dsimp at hr
      omega) hι (by rw [(F base).dimension]; omega)
  refine ⟨v, ?_, fun i => (F i).good_line hN (hv i)⟩
  intro he
  exact hv base (by rw [he]; exact Submodule.zero_mem _)

end CoboundaryExpanders.SphericalOpposition

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma safe_filling (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (r : ℕ) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded (F.safeComplex v).faces r)) (hz : rawBoundary c = 0) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+1)) ∧
      rawBoundary b = c ∧ size b ≤ carrierBound r * size c := by
  classical
  let T := carrierMap (F.carrierApex v)
  have hsingle (s : Finset (Submodule K V)) (hs : s ∈ (F.safeComplex v).faces) :
      T (Finsupp.single s 1) ∈ supported (graded F.complex.faces (s.card+1)) := by
    have hb := carrierFill_supported (F.safeComplex v) (F.carrier v) (F.carrierApex v)
      (F.self_mem_carrier v) (fun _ _ _ h => F.carrier_mono v h)
      (F.carrier_cone hN v hv) s hs
    have hcarr : graded (F.carrier v s) (s.card+1) ⊆ graded F.complex.faces (s.card+1) :=
      fun _ ht => ⟨ht.1.1, ht.2⟩
    simpa [T] using supported_mono hcarr hb
  refine ⟨T c, ?_, ?_, ?_⟩
  · apply map_supported T (graded (F.safeComplex v).faces r) _ _ c hc
    intro s hs a
    have he : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
    rw [he, map_smul]
    apply Submodule.smul_mem
    simpa [hs.2] using hsingle s hs.1
  · have hh := LinearMap.congr_fun (carrierMap_contraction (F.carrierApex v)) c
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hz, map_zero, add_zero] using hh
  · apply size_map_le T (graded (F.safeComplex v).faces r) (carrierBound r) _ c hc
    intro s hs
    simpa [T, hs.2] using carrierFill_size (F.carrierApex v) s

lemma no_top_filling [Fintype K] [Fintype V] (F : CompleteFlag K V N)
    (hN : 1 < N) (r : ℕ) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded (allowed F.complex F.TopBad ∅).faces r))
    (hz : rawBoundary c = 0) (hq : 1+r*size c < Fintype.card K) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+1)) ∧
      rawBoundary b = c ∧ size b ≤ carrierBound r * size c := by
  classical
  have hvert (W : Submodule K V) (hW : W ∈ vertices c) :
      F.Good W ∧ finrank K W + 1 < N := by
    obtain ⟨s, hs, hWs⟩ := Finset.mem_biUnion.mp hW
    have hsf := (mem_supported _ _).mp hc s (Finsupp.mem_support_iff.mp hs)
    have hg := hsf.1.1.1 W hWs
    have hne : finrank K W ≠ N-1 := fun hr =>
      Finset.notMem_empty W (hsf.1.2 W hWs ⟨hg, hr⟩)
    exact ⟨hg, by have := hg.2.1; omega⟩
  let Z : Submodule K V := F.space ⟨N-1, by omega⟩
  let S := insert Z ((vertices c).image F.forbidden)
  have hS : ∀ P ∈ S, P ≠ ⊤ := by
    intro P hP
    rcases Finset.mem_insert.mp hP with he | hP
    · subst P
      intro he
      have hr := F.rank ⟨N-1, by omega⟩
      change finrank K Z = N-1 at hr
      rw [he, finrank_top, F.dimension] at hr
      omega
    · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hP
      exact F.forbidden_ne_top W (hvert W hW).1.2.2 (hvert W hW).1.2.1
  have hcard : S.card < Fintype.card K := by
    have hi := Finset.card_insert_le Z ((vertices c).image F.forbidden)
    have him := Finset.card_image_le (s := vertices c) (f := F.forbidden)
    have hv := vertices_card_le (allowed F.complex F.TopBad ∅).faces r c hc
    dsimp [S]
    omega
  obtain ⟨v, hv⟩ := exists_vector_avoiding_finset S hS hcard (by rw [F.dimension]; omega)
  apply F.safe_filling hN v (hv Z (Finset.mem_insert_self _ _)) r c _ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1.1, ?_⟩, (hc s hs).2⟩
  intro W hW
  have hWv := mem_vertices c s hs W hW
  refine ⟨(hvert W hWv).2, ?_⟩
  exact hv (F.forbidden W) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨W, hWv, rfl⟩))

lemma hyperplane_link_filling (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.TopBad W) (n R r : ℕ)
    (H : BoundedCone (F.lower W hW.1.2.2).complex n R) (hr : r ≤ n)
    (c : Raw (Submodule K V)) (hc : c ∈ supported (graded F.complex.faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ b : Raw (Submodule K V),
      b ∈ supported (graded {s | s ∈ F.complex.faces ∧
        (∀ A ∈ s, ¬F.TopBad A) ∧ insert W s ∈ F.complex.faces} (r+1)) ∧
      rawBoundary b = link W c ∧ size b ≤ R * size c := by
  classical
  let L := F.lower W hW.1.2.2
  let P : Set (Finset (Submodule K V)) :=
    {s | s ∈ F.complex.faces ∧ ∀ A ∈ s, A < W}
  let f : Submodule K W → Submodule K V := Submodule.map W.subtype
  let g : Submodule K V → Submodule K W := Submodule.comap W.subtype
  have hinj : Function.Injective f := Submodule.map_injective_of_injective W.injective_subtype
  have hl : link W c ∈ supported (graded P r) := by
    apply link_graded W F.complex.faces P r _ c hc
    intro s hs hWs
    exact ⟨F.complex.downward hs (Finset.erase_subset _ _), F.hyperplane_link_lower W hW.2 s hs hWs⟩
  let a := relabel g (link W c)
  have ha : a ∈ supported (graded L.complex.faces r) := by
    apply relabel_graded g P L.complex.faces r _ _ _ hl
    · intro s hs
      exact F.lower_face_comap W hW.1.2.2 s hs.1 hs.2
    · intro s hs
      exact comap_injOn_lower W s (fun A hA => (hs.2 A hA).le)
  have hret : relabel f a = link W c := by
    apply relabel_retraction f g (graded P r) _ _ hl
    intro s hs A hA
    exact map_comap_lower W A (hs.1.2 A hA).le
  have haz : rawBoundary a = 0 := by
    apply relabel_injective f hinj
    rw [map_zero]
    have nat := LinearMap.congr_fun (relabel_boundary f hinj) a
    change rawBoundary (relabel f a) = relabel f (rawBoundary a) at nat
    rw [← nat, hret, link_cycle W c hz]
  let b := relabel f (H.hom a)
  refine ⟨b, ?_, ?_, ?_⟩
  · apply relabel_graded f L.complex.faces _ (r+1) _ (fun _ _ => hinj.injOn)
      (H.hom a) (H.map_graded r hr a ha)
    intro s hs
    have hm := F.lower_face_map W hW.1.2.2 s hs
    refine ⟨hm.1, ?_, F.insert_greatest_face W hW.1 _ hm.1 (fun A hA => (hm.2 A hA).le)⟩
    intro A hA hbad
    have hrank := Submodule.finrank_strictMono (hm.2 A hA)
    have hArank := hbad.2
    change finrank K A < finrank K W at hrank
    rw [hW.2, hArank] at hrank
    exact Nat.lt_irrefl _ hrank
  · have nat := LinearMap.congr_fun (relabel_boundary f hinj) (H.hom a)
    change rawBoundary b = relabel f (rawBoundary (H.hom a)) at nat
    rw [nat, H.fills r hr a ha haz, hret]
  · calc
      size b ≤ size (H.hom a) := relabel_size f _
      _ ≤ R * size a := H.size_apply r hr a ha
      _ ≤ R * size (link W c) := Nat.mul_le_mul_left R (relabel_size g _)
      _ ≤ R * size c := Nat.mul_le_mul_left R (link_size W c)

lemma small_filling [Fintype K] [Fintype V] (F : CompleteFlag K V N)
    (hN : 1 < N) (n R r S : ℕ)
    (H : ∀ W, ∀ hW : F.TopBad W, BoundedCone (F.lower W hW.1.2.2).complex n R)
    (hr : r ≤ n) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded F.complex.faces (r+1))) (hz : rawBoundary c = 0)
    (hsize : size c ≤ S) (hq : fieldBound R (r+1) S < Fintype.card K) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+2)) ∧
      rawBoundary b = c ∧ size b ≤ fillingBound R (r+1) S := by
  classical
  let A := (vertices c).filter F.TopBad
  have hA : ∀ W ∈ A, F.TopBad W := fun _ h => (Finset.mem_filter.mp h).2
  have hcA : c ∈ supported (graded (allowed F.complex F.TopBad A).faces (r+1)) := by
    rw [mem_supported] at hc ⊢
    intro s hs
    refine ⟨⟨(hc s hs).1, ?_⟩, (hc s hs).2⟩
    intro W hW hbad
    exact Finset.mem_filter.mpr ⟨mem_vertices c s hs W hW, hbad⟩
  obtain ⟨e, c', he, hc', hz', hec, htotal⟩ :=
    removeBad F.complex F.TopBad (r+1) R
      (fun W hW c hc hz => F.hyperplane_link_filling W hW n R r (H W hW) hr c hc hz)
      A hA c hcA hz
  have hAc : A.card ≤ (r+1)*S :=
    (Finset.card_filter_le _ _).trans ((vertices_card_le F.complex.faces (r+1) c hc).trans
      (Nat.mul_le_mul_left (r+1) hsize))
  have hE : size e + size c' ≤ eliminationBound R (r+1) S := by
    apply htotal.trans
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 0 < 2*R+2) hAc) hsize
  have hcE : size c' ≤ eliminationBound R (r+1) S := (Nat.le_add_left _ _).trans hE
  have hq' : 1+(r+1)*size c' < Fintype.card K :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left (r+1) hcE) 1).trans_lt hq
  obtain ⟨b, hb, hdb, hsz⟩ := F.no_top_filling hN (r+1) c' hc' hz' hq'
  refine ⟨e+b, Submodule.add_mem _ he hb, ?_, ?_⟩
  · rw [map_add, hdb, hec]
  · have hadd := size_add_le e b
    have hbE := hsz.trans (Nat.mul_le_mul_left (carrierBound (r+1)) hcE)
    dsimp [fillingBound]
    nlinarith

theorem exists_uniform_cones (n : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K]
      (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V],
      ∀ (N : ℕ) (F : CompleteFlag K V N), n+2 ≤ N → Q < Fintype.card K →
        Nonempty (BoundedCone F.complex n R) := by
  classical
  induction n with
  | zero =>
    refine ⟨1, 1, ?_⟩
    intro K _ _ V _ _ _ _ N F hN hq
    obtain ⟨v, hv, hg⟩ := exists_common_good_line (ι := Unit) (fun _ => F) (by omega)
      (by simpa using hq)
    refine ⟨BoundedCone.initial F.complex (Submodule.span K {v}) ?_⟩
    refine ⟨?_, ?_⟩
    · intro W hW
      have he : W = Submodule.span K {v} := Finset.mem_singleton.mp hW
      exact he ▸ hg ()
    · simp
  | succ n ih =>
    obtain ⟨Q, R, hcones⟩ := ih
    let S := 1+R*(n+1)
    refine ⟨max Q (fieldBound R (n+1) S), max R (fillingBound R (n+1) S), ?_⟩
    intro K _ _ V _ _ _ _ N F hN hq
    have hqQ : Q < Fintype.card K := (Nat.le_max_left _ _).trans_lt hq
    have hqF : fieldBound R (n+1) S < Fintype.card K := (Nat.le_max_right _ _).trans_lt hq
    let H : BoundedCone F.complex n R := (hcones K V N F (by omega) hqQ).some
    have hlower (W : Submodule K V) (hW : F.TopBad W) :
        Nonempty (BoundedCone (F.lower W hW.1.2.2).complex n R) := by
      apply hcones K W (finrank K W) (F.lower W hW.1.2.2)
      · rw [hW.2]
        omega
      · exact hqQ
    exact ⟨H.extend (fillingBound R (n+1) S)
      (fun c hc hz hs => F.small_filling (by omega) n R n S
        (fun W hW => (hlower W hW).some) le_rfl c hc hz hs hqF)⟩

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Elementary matrices, Euclidean generation, block matrices, and residue-field pivot arguments.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary
variable {A : Type*} [CommRing A] {n : ℕ}

theorem E_upper_one_mem (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i.val + 1 = j.val), E (show i ≠ j by intro he; subst j; omega) (1 : A) ∈ H)
    {i j : Fin n} (hij : i < j) : E hij.ne (1 : A) ∈ H := by
  generalize hdiff : j.val - i.val = r
  induction r using Nat.strong_induction_on generalizing i j with
  | h r ih =>
    by_cases hadj : i.val + 1 = j.val
    · exact hE i j hadj
    · let k : Fin n := ⟨j.val - 1, by omega⟩
      have hik : i < k := by dsimp [k]; change i.val < j.val - 1; omega
      have hkj : k.val + 1 = j.val := by dsimp [k]; omega
      have hkj' : k < j := by change k.val < j.val; omega
      have hk := ih (k.val - i.val) (by omega) hik rfl
      simpa only [mul_one] using E_path_mem H hik.ne hkj'.ne hij.ne hk (hE k j hkj)

end CoboundaryExpanders.Elementary

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Elementary
variable {A F : Type*} [CommRing A] [CommRing F] {n : ℕ}

theorem off_clear_step (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : g ∈ B)
    (k : ℕ) (hk : k < n * n) (hc : OffCleared g k) :
    ∃ e ∈ H, e * g ∈ B ∧ OffCleared (e * g) (k + 1) := by
  have hn : 0 < n := by nlinarith
  let j : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk⟩
  let i : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
  have hkij : j.val * n + i.val = k := by
    dsimp [i, j]
    simpa [Nat.mul_comm] using Nat.div_add_mod k n
  by_cases hij : i = j
  · refine ⟨1, H.one_mem, by simpa using hg, ?_⟩
    rw [one_mul]
    intro a b hab hkey
    apply hc a b hab
    have hne : b.val * n + a.val ≠ k := by
      intro he
      have hai : a = i := by
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt a.isLt] using this
      have hbj : b = j := by
        apply Fin.ext
        have := congrArg (fun r => r / n) he
        simpa only [Nat.mul_comm b.val n, Nat.mul_add_div hn,
          Nat.div_eq_of_lt a.isLt, add_zero] using this
      exact hab (hai.trans (hij.trans hbj.symm))
    omega
  · obtain ⟨u, hu⟩ := hunit (g j j) (by simpa using hB g hg j j le_rfl)
    let c : A := -g i j * (↑(u⁻¹) : A)
    have he : E hij c ∈ H := by
      apply hE
      intro hji
      simp [c, hB g hg i j hji.le, hij]
    refine ⟨E hij c, he, B.mul_mem (hHB he) hg, ?_⟩
    intro a b hab hkey
    rw [E_mul_apply]
    by_cases ha : a = i
    · subst a
      rw [ite_eq_left rfl]
      by_cases hb : b = j
      · subst b
        rw [← hu]
        dsimp [c]
        rw [mul_assoc, Units.inv_mul, mul_one, add_neg_cancel]
      · have hbj : b.val < j.val := by
          have hbval : b.val ≠ j.val := Fin.val_ne_of_ne hb
          have hb_le : b.val ≤ j.val := by
            by_contra hnot
            have hlt : j.val + 1 ≤ b.val := by omega
            have hmul := Nat.mul_le_mul_right n hlt
            nlinarith
          omega
        rw [hc j b (ne_of_gt (show b < j from hbj)) (by
          have hmul := Nat.mul_le_mul_right n (by omega : b.val + 1 ≤ j.val)
          have hjlt := j.isLt
          nlinarith), mul_zero, add_zero]
        apply hc i b hab
        have hmul := Nat.mul_le_mul_right n (by omega : b.val + 1 ≤ j.val)
        nlinarith
    · rw [ite_eq_right ha, add_zero]
      apply hc a b hab
      have hne : b.val * n + a.val ≠ k := by
        intro he
        apply ha
        apply Fin.ext
        have := congrArg (fun r => r % n) he
        simpa [Nat.add_mod, Nat.mod_eq_of_lt a.isLt] using this
      omega

theorem diagonalize_iwahori (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) A) (hg : g ∈ B) :
    ∃ h ∈ H, h * g ∈ B ∧ ∀ i j, i ≠ j → (h * g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n * n → ∃ h ∈ H, h * g ∈ B ∧ OffCleared (h * g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1, H.one_mem, by simpa using hg, by intro i j h h'; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hb, hc⟩ := ih (by omega)
      obtain ⟨e, he, hb', hc'⟩ := off_clear_step π B H hHB hB hunit hE
        (h * g) hb k (by omega) hc
      exact ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using hb',
        by simpa only [mul_assoc] using hc'⟩
  obtain ⟨h, hh, hb, hc⟩ := hsteps _ le_rfl
  refine ⟨h, hh, hb, fun i j hij => hc i j hij ?_⟩
  have hi := i.isLt
  have hj := j.isLt
  nlinarith

theorem D_mem (π : A →+* F) (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    {i j : Fin n} (hij : i < j) (u : Aˣ) (hu : π (↑u : A) = 1) : D hij.ne u ∈ H := by
  unfold D
  apply H.mul_mem
  · apply H.mul_mem
    · apply H.mul_mem
      · exact hE _ _ _ _ (by intro h; exact False.elim ((lt_asymm hij h)))
      · exact hE _ _ _ _ (by intro _; simp [hu])
    · exact hE _ _ _ _ (by intro h; exact False.elim ((lt_asymm hij h)))
  · exact hE _ _ _ _ (by intro _; simp [hu])

theorem diagonal_iwahori_mem (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) A) (hg : g ∈ B)
    (hdiag : ∀ i j, i ≠ j → g i j = 0) : g ∈ H := by
  have hsteps : ∀ k, k ≤ n → ∃ h ∈ H, h * g ∈ B ∧
      (∀ i j, i ≠ j → (h * g) i j = 0) ∧
      (∀ i : Fin (n + 1), i.val < k → (h * g) i i = 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, by simpa using hg, by simpa using hdiag,
        by intro i hi; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hh, hb, hd, hc⟩ := ih (by omega)
      let i : Fin (n + 1) := ⟨k, by omega⟩
      have hilast : i < Fin.last n := by change k < n; omega
      obtain ⟨u, hu⟩ := hunit ((h * g) i i) (by simpa using hB (h * g) hb i i le_rfl)
      have hπu : π (u : A) = 1 := by rw [hu]; simpa using hB (h * g) hb i i le_rfl
      have hπinv : π (↑(u⁻¹) : A) = 1 := by
        have := congrArg π (Units.mul_inv u)
        simpa only [map_mul, map_one, hπu, one_mul] using this
      let e := D hilast.ne u⁻¹
      have he : e ∈ H := D_mem π H hE hilast u⁻¹ hπinv
      refine ⟨e * h, H.mul_mem he hh, by simpa only [mul_assoc] using B.mul_mem (hHB he) hb,
        ?_, ?_⟩
      · intro a b hab
        rw [mul_assoc, D_mul_apply, hd a b hab, mul_zero]
      · intro a ha
        rw [mul_assoc, D_mul_apply]
        by_cases hai : a = i
        · subst a
          rw [ite_eq_left rfl, ← hu]
          exact Units.inv_mul u
        · have halast : a ≠ Fin.last n := by intro heq; subst a; simp only [Fin.val_last] at ha; omega
          rw [ite_eq_right hai, ite_eq_right halast, one_mul]
          apply hc
          have hne : a.val ≠ k := fun h => hai (Fin.ext h)
          omega
  obtain ⟨h, hh, hb, hd, hc⟩ := hsteps n le_rfl
  have hmatrix : (h * g).val = Matrix.diagonal (fun i => (h * g) i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · rw [hd i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, (h * g) i i = (1 : A) := by
    rw [← Matrix.det_diagonal, ← hmatrix]
    exact (h * g).property
  have hfirst : ∀ i : Fin n, (h * g) i.castSucc i.castSucc = 1 := fun i => hc _ i.isLt
  have hlast : (h * g) (Fin.last n) (Fin.last n) = 1 := by
    simpa only [Fin.prod_univ_castSucc, hfirst, Finset.prod_const_one, one_mul] using hdet
  have heq : h * g = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (h * g) i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      by_cases hilast : i = Fin.last n
      · subst i; exact hlast
      · apply hc
        have := i.isLt
        have := Fin.val_ne_of_ne hilast
        simp only [Fin.val_last] at this
        omega
    · rw [hd i j hij, Matrix.one_apply_ne hij]
  rw [eq_inv_of_mul_eq_one_right heq]
  exact H.inv_mem hh

theorem iwahori_mem_of_roots (π : A →+* F)
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) A)) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → π (g i j) = if i = j then 1 else 0)
    (hunit : ∀ a : A, π a = 1 → IsUnit a)
    (hE : ∀ i j (h : i ≠ j) c, (j < i → π c = 0) → E h c ∈ H) : B ≤ H := by
  intro g hg
  obtain ⟨h, hh, hb, hd⟩ := diagonalize_iwahori π B H hHB hB hunit hE g hg
  have hm := diagonal_iwahori_mem π B H hHB hB hunit hE (h * g) hb hd
  simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem hh) hm

end CoboundaryExpanders.Elementary

end

open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Links
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutVertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coset-link identifications, product and cut models, and all proper-link cone bounds.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains

open Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
lemma complex_eq {X Y : CoboundaryExpanders.InfiniteChains.Complex V} (h : X.faces = Y.faces) : X = Y := by
  cases X; cases Y; cases h; rfl

lemma faceLink_empty (X : CoboundaryExpanders.InfiniteChains.Complex V) : X.faceLink ∅ X.empty_mem = X := by
  apply complex_eq
  ext s
  simp [Complex.faceLink]

lemma faceLink_iterated (X : CoboundaryExpanders.InfiniteChains.Complex V) {s a : Finset V} (hs : s ∈ X.faces)
    (ha : a ∈ (X.faceLink s hs).faces) :
    (X.faceLink s hs).faceLink a ha = X.faceLink (s∪a) ha.2 := by
  apply complex_eq
  ext t
  change (Disjoint a t ∧ Disjoint s (a∪t) ∧ s∪(a∪t) ∈ X.faces) ↔
    (Disjoint (s∪a) t ∧ (s∪a)∪t ∈ X.faces)
  simp only [Finset.disjoint_union_left,Finset.disjoint_union_right,ha.1,true_and,Finset.union_assoc]
  tauto

namespace Join

omit [DecidableEq V] [DecidableEq W] in
lemma disjoint_split (s t : Finset (W ⊕ V)) :
    Disjoint s t ↔ Disjoint s.toLeft t.toLeft ∧ Disjoint s.toRight t.toRight := by
  rw [Finset.disjoint_left,Finset.disjoint_left,Finset.disjoint_left]
  constructor
  · intro h
    constructor
    · intro v hv hv'; exact h (by simpa using hv) (by simpa using hv')
    · intro v hv hv'; exact h (by simpa using hv) (by simpa using hv')
  · rintro ⟨hL,hR⟩ (v|v) hv hv'
    · exact hL (by simpa using hv) (by simpa using hv')
    · exact hR (by simpa using hv) (by simpa using hv')

lemma link_eq {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {s : Finset (W ⊕ V)}
    (hs : s ∈ (complex X Y).faces) :
    (complex X Y).faceLink s hs =
      complex (X.faceLink s.toLeft hs.1) (Y.faceLink s.toRight hs.2) := by
  apply complex_eq
  ext t
  change (Disjoint s t ∧ (s∪t).toLeft ∈ X.faces ∧ (s∪t).toRight ∈ Y.faces) ↔
    (Disjoint s.toLeft t.toLeft ∧ s.toLeft∪t.toLeft ∈ X.faces) ∧
      (Disjoint s.toRight t.toRight ∧ s.toRight∪t.toRight ∈ Y.faces)
  rw [disjoint_split,Finset.toLeft_union,Finset.toRight_union]
  tauto

end Join
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma linkComplex_eq (A : Finset I) : linkComplex H A =
    (complex H).faceLink (face H 1 A) (standard_face_mem H A) := by
  apply InfiniteChains.complex_eq
  ext t
  change Disjoint t (face H 1 A) ∧ IsFace H (t ∪ face H 1 A) ↔
    Disjoint (face H 1 A) t ∧ IsFace H (face H 1 A ∪ t)
  rw [disjoint_comm,Finset.union_comm]

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

omit [DecidableEq I] in
lemma coset_pure [Fintype I] :
    (∃ t, IsFace H t ∧ t.card = Fintype.card I) ∧
      ∀ s, IsFace H s → ∃ t, IsFace H t ∧ t.card = Fintype.card I ∧ s ⊆ t := by
  constructor
  · exact ⟨face H 1 Finset.univ,⟨1,_,rfl⟩,by simp⟩
  · rintro s ⟨g,A,rfl⟩
    exact ⟨face H g Finset.univ,⟨g,_,rfl⟩,by simp,Finset.image_mono _ (Finset.subset_univ _)⟩

omit [DecidableEq I] in
lemma chamber_transitive [Fintype I] {s t : Finset (Vertex H)}
    (hs : IsFace H s) (ht : IsFace H t) (hsc : s.card = Fintype.card I) (htc : t.card = Fintype.card I) :
    ∃ g : G, g • s = t := by
  obtain ⟨g,A,rfl⟩ := hs
  obtain ⟨h,B,rfl⟩ := ht
  have ha : A = Finset.univ := Finset.eq_univ_of_card A (by simpa using hsc)
  have hb : B = Finset.univ := Finset.eq_univ_of_card B (by simpa using htc)
  subst A; subst B
  exact ⟨h*g⁻¹,by simp [mul_assoc]⟩

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.InfiniteChains

section
open Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma RankBound.link {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hX : RankBound X N)
    {s : Finset V} (hs : s ∈ X.faces) : RankBound (X.faceLink s hs) (N-s.card) := by
  intro a ha
  have h := hX (s∪a) ha.2
  rw [Finset.card_union_of_disjoint ha.1] at h
  omega

lemma RankBound.terminal {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hX : RankBound X N)
    {s : Finset V} (hs : s ∈ X.faces) (hN : s.card = N) :
    ∀ a ∈ (X.faceLink s hs).faces, a = ∅ := by
  intro a ha
  have h := hX.link hs a ha
  rw [hN,Nat.sub_self] at h
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)

lemma AllLinkCones.weaken {X : CoboundaryExpanders.InfiniteChains.Complex V} {N R S : ℕ} (h : AllLinkCones X N R) (hS : R ≤ S) :
    AllLinkCones X N S := by
  intro s hs hn
  exact ⟨(h s hs hn).some.weaken le_rfl hS⟩

lemma Cone.FaceModel.pushAllLinks {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N R : ℕ} (h : AllLinkCones X N R) : AllLinkCones Y N R := by
  intro t ht hn
  obtain ⟨s,hs,rfl⟩ := M.cover t ht
  rw [Finset.card_image_of_injective _ M.injective] at hn ⊢
  exact ⟨(M.linkModel s hs).pushCone (h s hs hn).some⟩

lemma Cone.FaceModel.pullAllLinks {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N R : ℕ} (h : AllLinkCones Y N R) : AllLinkCones X N R := by
  intro s hs hn
  have hc : (s.image M.vertex).card < N := by rwa [Finset.card_image_of_injective _ M.injective]
  have H := h (s.image M.vertex) ((M.face_iff s).mpr hs) hc
  rw [Finset.card_image_of_injective _ M.injective] at H
  exact ⟨(M.linkModel s hs).pullCone H.some⟩

namespace Join

theorem allLinkCones {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {A B R S : ℕ}
    (hX : RankBound X A) (hY : RankBound Y B)
    (hCX : AllLinkCones X A R) (hCY : AllLinkCones Y B S) :
    AllLinkCones (complex X Y) (A+B) (R+S+(1+R*(A+1))*S) := by
  intro s hs hn
  have hL := hX s.toLeft hs.1
  have hR := hY s.toRight hs.2
  have hC := Finset.card_toLeft_add_card_toRight (u:=s)
  rw [link_eq hs]
  by_cases hA : s.toLeft.card = A
  · have hB : s.toRight.card < B := by omega
    have he : A+B-s.card-1 = B-s.toRight.card-1 := by omega
    rw [he]
    exact ⟨((emptyLeftModel (hX.terminal hs.1 hA)).pushCone (hCY _ hs.2 hB).some).weaken le_rfl (by omega)⟩
  by_cases hB : s.toRight.card = B
  · have hAl : s.toLeft.card < A := by omega
    have he : A+B-s.card-1 = A-s.toLeft.card-1 := by omega
    rw [he]
    exact ⟨((emptyRightModel (hY.terminal hs.2 hB)).pushCone (hCX _ hs.1 hAl).some).weaken le_rfl (by omega)⟩
  have hAl : s.toLeft.card < A := by omega
  have hBl : s.toRight.card < B := by omega
  have he : A+B-s.card-1 = (A-s.toLeft.card-1)+(B-s.toRight.card-1)+1 := by omega
  rw [he]
  refine ⟨(boundedCone (hCX _ hs.1 hAl).some (hCY _ hs.2 hBl).some).weaken le_rfl ?_⟩
  apply max_le
  · omega
  · have hh := Nat.mul_le_mul_right S (Nat.add_le_add_left
      (Nat.mul_le_mul_left R (show A-s.toLeft.card-1+1 ≤ A+1 by omega)) 1)
    omega

end Join
end

open Cone
variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
lemma singleton_mem_of_mem_face {X : CoboundaryExpanders.InfiniteChains.Complex V} {s : Finset V} (hs : s ∈ X.faces)
    {v : V} (hv : v ∈ s) : {v} ∈ X.faces := X.downward hs (Finset.singleton_subset_iff.mpr hv)

lemma faceLink_congr {X : CoboundaryExpanders.InfiniteChains.Complex V} {s t : Finset V} (hs : s ∈ X.faces) (ht : t ∈ X.faces)
    (h : s = t) : X.faceLink s hs = X.faceLink t ht := by subst t; rfl

lemma AllLinkCones.vertexCriterion {X : CoboundaryExpanders.InfiniteChains.Complex V} {N R : ℕ} (hN : 0 < N)
    (hBase : Nonempty (BoundedCone X (N-1) R))
    (hVertex : ∀ v : V, ∀ hv : {v} ∈ X.faces,
      AllLinkCones (X.faceLink {v} hv) (N-1) R) : AllLinkCones X N R := by
  intro s hs hn
  by_cases he : s = ∅
  · subst s
    simpa only [faceLink_empty,Finset.card_empty,Nat.sub_zero] using hBase
  obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hvx := singleton_mem_of_mem_face hs hv
  have hu : {v} ∪ s.erase v = s := by simp [Finset.insert_erase hv]
  have ht : s.erase v ∈ (X.faceLink {v} hvx).faces := by
    constructor
    · simp
    · rwa [hu]
  have hc : (s.erase v).card = s.card-1 := Finset.card_erase_of_mem hv
  have hlt : (s.erase v).card < N-1 := by have hp := Finset.card_pos.mpr ⟨v,hv⟩; omega
  have H := hVertex v hvx (s.erase v) ht hlt
  rw [faceLink_iterated,faceLink_congr ht.2 hs hu] at H
  have hp := Finset.card_pos.mpr ⟨v,hv⟩
  have he : (N-1)-(s.erase v).card-1 = N-s.card-1 := by omega
  rwa [he] at H

end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma rankBound [Fintype I] : InfiniteChains.RankBound (complex H) (Fintype.card I) := by
  rintro s ⟨g,A,rfl⟩
  rw [face_card]
  exact Finset.card_le_univ _

lemma standard_link_eq (i : I) : linkComplex H {i} =
    (complex H).faceLink {vertex H 1 i} (standard_singleton_face H i) := by
  simpa only [face,Finset.image_singleton] using linkComplex_eq H {i}

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag TypedCosetFaces InfiniteChains Cone
open scoped Pointwise
variable {K : Type} [Field K] {N : ℕ}

lemma card_cut (N : ℕ) : Fintype.card (Cut N) = N-1 := by
  rw [Fintype.card_congr (cutTypeEquiv (N:=N)),Fintype.card_fin]
lemma cut_rankBound : RankBound (TypedCosetFaces.complex (cutGroups K N)) (N-1) := by
  simpa only [card_cut] using TypedCosetFaces.rankBound (cutGroups K N)

lemma cut_middle_link_cones {a b R S : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hA : AllLinkCones (TypedCosetFaces.complex (cutGroups K a)) (a-1) R)
    (hB : AllLinkCones (TypedCosetFaces.complex (cutGroups K b)) (b-1) S) :
    AllLinkCones (linkComplex (cutGroups K (a+b)) {middleCut ha hb})
      ((a-1)+(b-1)) (R+S+(1+R*((a-1)+1))*S) := by
  have hj := Join.allLinkCones cut_rankBound cut_rankBound hA hB
  exact (singleLinkModel _ _).pushAllLinks
    ((cutProductLinkModel ha hb).pushAllLinks
      ((productModel (cutGroups K a) (cutGroups K b)).pullAllLinks hj))

theorem uniform_cut_allLinkCones (N : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K], Q < Fintype.card K →
      AllLinkCones (TypedCosetFaces.complex (cutGroups K N)) (N-1) R := by
  classical
  induction N using Nat.strong_induction_on with | h N ih =>
  by_cases hN : N ≤ 1
  · exact ⟨0,0,fun _ _ _ _ s _ hs => by omega⟩
  have hN2 : 2 ≤ N := by omega
  obtain ⟨Q0,R0,h0⟩ := exists_uniform_cones (N-2)
  choose q r hr using fun i : Fin N => ih i.val i.isLt
  let QL := ∑ i : Fin N, q i
  let L := ∑ i : Fin N, r i
  let B := L+L+(1+L*(N+1))*L
  refine ⟨max Q0 QL,max R0 B,?_⟩
  intro K _ _ hQ
  have hsmall (a : ℕ) (ha : a < N) :
      AllLinkCones (TypedCosetFaces.complex (cutGroups K a)) (a-1) L := by
    have hq : q ⟨a,ha⟩ ≤ QL := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    have hr' : r ⟨a,ha⟩ ≤ L := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    exact (hr ⟨a,ha⟩ K (lt_of_le_of_lt (hq.trans (le_max_right _ _)) hQ)).weaken hr'
  apply AllLinkCones.vertexCriterion (by omega : 0 < N-1)
  · have H := h0 K (Fin N → K) N (stdFlag K N) (by omega)
      (lt_of_le_of_lt (le_max_left _ _) hQ)
    have hh := cutSphericalModel (K:=K) (N:=N) |>.pullCone H.some
    have he : N-1-1 = N-2 := by omega
    rw [he]
    exact ⟨hh.weaken le_rfl (le_max_left _ _)⟩
  intro v hv
  rcases v with ⟨c,v⟩
  induction v using Quotient.inductionOn with | h g =>
  have hstandard : AllLinkCones (linkComplex (cutGroups K N) {c}) (N-1-1) (max R0 B) := by
    rcases c with ⟨a,ha,haN⟩
    obtain ⟨b,hNb⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt haN)
    subst N
    have hb : 0 < b := by omega
    have hbN : b < a+b := by omega
    have hc := cut_middle_link_cones ha hb (hsmall a haN) (hsmall b hbN)
    have he : (a-1)+(b-1) = a+b-1-1 := by omega
    rw [he] at hc
    refine hc.weaken ?_
    apply le_trans _ (le_max_right _ _)
    dsimp [B]
    gcongr
    omega
  rw [standard_link_eq] at hstandard
  have hm := (actionModel (cutGroups K N) g).linkModel {vertex (cutGroups K N) 1 c}
    (standard_singleton_face _ _)
  have hh := hm.pushAllLinks hstandard
  have he : (actionModel (cutGroups K N) g).vertex (vertex (cutGroups K N) 1 c) =
      vertex (cutGroups K N) g c := by
    change g • vertex (cutGroups K N) 1 c = _
    rw [smul_vertex,mul_one]
  have hi : ({vertex (cutGroups K N) 1 c} : Finset _).image
      (actionModel (cutGroups K N) g).vertex = {vertex (cutGroups K N) g c} := by
    rw [Finset.image_singleton,he]
  rw [faceLink_congr _ hv hi] at hh
  exact hh

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.InfiniteChains
open Cone
variable {V : Type} [DecidableEq V]

lemma ProperLinkCones.vertexCriterion {X : CoboundaryExpanders.InfiniteChains.Complex V} {N R : ℕ}
    (hVertex : ∀ v : V, ∀ hv : {v} ∈ X.faces,
      AllLinkCones (X.faceLink {v} hv) (N-1) R) : ProperLinkCones X N R := by
  intro s hne hs hn
  obtain ⟨v,hv⟩ := hne
  have hvx := singleton_mem_of_mem_face hs hv
  have hu : {v} ∪ s.erase v = s := by simp [Finset.insert_erase hv]
  have ht : s.erase v ∈ (X.faceLink {v} hvx).faces := by
    constructor
    · simp
    · rwa [hu]
  have hc : (s.erase v).card = s.card-1 := Finset.card_erase_of_mem hv
  have hp := Finset.card_pos.mpr ⟨v,hv⟩
  have hlt : (s.erase v).card < N-1 := by omega
  have H := hVertex v hvx (s.erase v) ht hlt
  rw [faceLink_iterated,faceLink_congr ht.2 hs hu] at H
  have he : (N-1)-(s.erase v).card-1 = N-s.card-1 := by omega
  rwa [he] at H
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma allVertexLinks_of_standard {N R : ℕ}
    (hs : ∀ i : I, AllLinkCones (linkComplex H {i}) N R) :
    ∀ v : Vertex H, ∀ hv : {v} ∈ (complex H).faces,
      AllLinkCones ((complex H).faceLink {v} hv) N R := by
  rintro ⟨i,v⟩ hv
  induction v using Quotient.inductionOn with | h g =>
  have hh := hs i
  rw [standard_link_eq] at hh
  have hh' := ((actionModel H g).linkModel {vertex H 1 i} (standard_singleton_face H i)).pushAllLinks hh
  have he : (actionModel H g).vertex (vertex H 1 i) = vertex H g i := by
    change g • vertex H 1 i = _
    rw [smul_vertex,mul_one]
  have hi : ({vertex H 1 i} : Finset _).image (actionModel H g).vertex = {vertex H g i} := by
    rw [Finset.image_singleton,he]
  rw [faceLink_congr _ hv hi] at hh'
  exact hh'
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open InfiniteChains Cone TypedCosetFaces SphericalOpposition.CompleteFlag MatrixOpposition

theorem uniform_actual_proper_link_cones (n : ℕ) (hn : 1 ≤ n) :
    ∃ Q R : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p →
      ∀ m : ℕ, 2 ≤ m →
        ProperLinkCones (TypedCosetFaces.complex (reducedLocalGroup p n hn m)) (n+1) R := by
  obtain ⟨Q,R,h⟩ := uniform_cut_allLinkCones (n+1)
  refine ⟨Q,R,?_⟩
  intro p hp hq m hm
  have hspherical := (cutSphericalModel (K:=ZMod p) (N:=n+1)).pushAllLinks
    (h (ZMod p) (by simpa only [ZMod.card] using hq))
  have hspherical' : AllLinkCones (stdFlag (ZMod p) (n+1)).complex n R := by
    simpa only [Nat.add_sub_cancel] using hspherical
  apply ProperLinkCones.vertexCriterion
  apply allVertexLinks_of_standard
  intro cut
  have hc := (sphericalLinkModel p n hn hm cut).pullAllLinks hspherical'
  have ha := (actualVertexLinkModel p n hn m cut).pushAllLinks hc
  simpa only [Nat.add_sub_cancel] using ha

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_LinkSpectrum
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Rank-two incidence geometry, weighted Rayleigh inequalities, and spectral bounds for links.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.RankTwo
variable {K : Type} [Field K] [Fintype K]

omit [Field K] in
lemma energy_nonneg (f : K → K → ℝ) : 0 ≤ energy f := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma affine_sum (x y x' : K) (h : x' ≠ x) (f : K → ℝ) :
    ∑ a, f (a*x'+(y-a*x)) = ∑ z, f z := by
  let e := (Equiv.mulRight₀ (x'-x) (sub_ne_zero.mpr h)).trans (Equiv.addRight y)
  apply Fintype.sum_equiv e
  intro a
  congr 1
  change a*x'+(y-a*x) = a*(x'-x)+y
  ring

lemma adjoint (f g : K → K → ℝ) : pairing (lineSum f) g = pairing f (pointSum g) := by
  unfold pairing lineSum pointSum
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Fintype.sum_equiv (Equiv.addLeft (a*x))
  intro b
  simp

attribute [local instance] OAI.CoboundaryExpanders.RankTwo.instDecidableEq_solutions
lemma gram (f : K → K → ℝ) (x y : K) :
    pointSum (lineSum f) x y =
      (Fintype.card K : ℝ) * f x y + ∑ x' ∈ Finset.univ.erase x, ∑ y', f x' y' := by
  classical
  unfold pointSum lineSum
  rw [Finset.sum_comm, ← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
  have he (x' : K) (hx' : x' ∈ Finset.univ.erase x) :
      ∑ a, f x' (a*x'+(y-a*x)) = ∑ y', f x' y' :=
    affine_sum x y x' (Finset.mem_erase.mp hx').1 (f x')
  rw [Finset.sum_congr rfl he]
  have hy (a : K) : a*x+(y-a*x) = y := by ring
  simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma gram_mean_zero (f : K → K → ℝ) (hf : ∑ x, ∑ y, f x y = 0) (x y : K) :
    pointSum (lineSum f) x y = (Fintype.card K : ℝ) * f x y - ∑ y', f x y' := by
  classical
  rw [gram]
  have h := Finset.sum_erase_add Finset.univ (fun x => ∑ y, f x y) (Finset.mem_univ x)
  rw [hf] at h
  linarith

omit [Field K] in
lemma energy_eq_pairing (f : K → K → ℝ) : energy f = pairing f f := by
  simp only [energy, pairing, pow_two]

theorem incidence_energy_identity (f : K → K → ℝ) (hf : ∑ x, ∑ y, f x y = 0) :
    energy (lineSum f) = (Fintype.card K : ℝ) * energy f - ∑ x, (∑ y, f x y)^2 := by
  rw [energy_eq_pairing, adjoint]
  simp only [pairing, gram_mean_zero f hf, mul_sub, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul]
  have h (x : K) : ∑ y, f x y * ((Fintype.card K : ℝ) * f x y) =
      (Fintype.card K : ℝ) * ∑ y, (f x y)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [h, ← Finset.mul_sum, ← pow_two, energy]

theorem incidence_energy_bound (f : K → K → ℝ) (hf : ∑ x, ∑ y, f x y = 0) :
    energy (lineSum f) ≤ (Fintype.card K : ℝ) * energy f := by
  rw [incidence_energy_identity f hf]
  have : 0 ≤ ∑ x, (∑ y, f x y)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

omit [Field K] in
lemma pairing_sq_le (f g : K → K → ℝ) : pairing f g ^ 2 ≤ energy f * energy g := by
  simpa only [Fintype.sum_prod_type, pairing, energy] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (K × K))
      (fun z => f z.1 z.2) (fun z => g z.1 z.2)

theorem incidence_pairing_bound (f g : K → K → ℝ) (hf : ∑ x, ∑ y, f x y = 0) :
    pairing (lineSum f) g ^ 2 ≤ (Fintype.card K : ℝ) * energy f * energy g := by
  exact (pairing_sq_le (lineSum f) g).trans
    (mul_le_mul_of_nonneg_right (incidence_energy_bound f hf) (energy_nonneg g))

lemma card_pos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos

lemma total_center (f : K → K → ℝ) : total (center f) = 0 := by
  have hq := card_pos (K := K)
  simp only [total, center, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

lemma energy_center (f : K → K → ℝ) :
    energy (center f) = energy f - (total f)^2 / (Fintype.card K : ℝ)^2 := by
  have hq := card_pos (K := K)
  have he (x y : K) : (center f x y)^2 = (f x y)^2 -
      (2 * total f / (Fintype.card K : ℝ)^2) * f x y +
      (total f / (Fintype.card K : ℝ)^2)^2 := by unfold center; ring
  simp only [energy, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change energy f - (2*total f/(Fintype.card K : ℝ)^2)*total f +
    (Fintype.card K : ℝ)*((Fintype.card K : ℝ)*(total f/(Fintype.card K : ℝ)^2)^2) = _
  unfold energy
  field_simp
  ring

lemma energy_center_le (f : K → K → ℝ) : energy (center f) ≤ energy f := by
  rw [energy_center]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

lemma total_lineSum (f : K → K → ℝ) :
    total (lineSum f) = (Fintype.card K : ℝ) * total f := by
  unfold total lineSum
  calc
    (∑ a, ∑ b, ∑ x, f x (a*x+b)) = ∑ a, ∑ x, ∑ b, f x (a*x+b) := by
      apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
    _ = ∑ a : K, ∑ x, ∑ y, f x y := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro x _
      exact Equiv.sum_comp (Equiv.addLeft (a*x)) (f x)
    _ = _ := by simp

lemma lineSum_center (f : K → K → ℝ) (a b : K) :
    lineSum (center f) a b = lineSum f a b - total f / (Fintype.card K : ℝ) := by
  have hq := card_pos (K := K)
  simp only [lineSum, center, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  congr 1
  field_simp

lemma incidence_center (f g : K → K → ℝ) :
    pairing (lineSum (center f)) (center g) =
      pairing (lineSum f) g - total f * total g / (Fintype.card K : ℝ) := by
  have hq := card_pos (K := K)
  have he (a b : K) : lineSum (center f) a b * center g a b =
      lineSum f a b * g a b - (total g / (Fintype.card K : ℝ)^2) * lineSum f a b -
      (total f / (Fintype.card K : ℝ)) * g a b +
      total f * total g / (Fintype.card K : ℝ)^3 := by
    rw [lineSum_center]
    unfold center
    field_simp
    ring
  simp only [pairing, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change pairing (lineSum f) g - (total g / (Fintype.card K : ℝ)^2)*total (lineSum f) -
    (total f / (Fintype.card K : ℝ))*total g +
    (Fintype.card K : ℝ)*((Fintype.card K : ℝ)*(total f*total g/(Fintype.card K : ℝ)^3)) = _
  rw [total_lineSum]
  unfold pairing
  field_simp
  ring

theorem opposition_rayleigh (f g : K → K → ℝ) (hfg : total f + total g = 0) :
    2 * pairing (lineSum f) g ≤
      Real.sqrt (Fintype.card K : ℝ) * (energy f + energy g) := by
  have hq := card_pos (K := K)
  have hsq := Real.sq_sqrt hq.le
  have hsqp := Real.sqrt_pos.mpr hq
  let c := pairing (lineSum (center f)) (center g)
  have hc : c^2 ≤ (Fintype.card K : ℝ) * energy (center f) * energy (center g) :=
    incidence_pairing_bound (center f) (center g) (total_center f)
  have he : 2*c ≤ Real.sqrt (Fintype.card K : ℝ) *
      (energy (center f) + energy (center g)) := by
    have h0 := energy_nonneg (center f)
    have h1 := energy_nonneg (center g)
    have h2 := sq_nonneg (energy (center f) - energy (center g))
    have h3 : 0 ≤ Real.sqrt (Fintype.card K : ℝ) *
        (energy (center f)+energy (center g)) := by positivity
    apply le_of_sq_le_sq _ h3
    simp only [mul_pow, hsq]
    nlinarith only [hc, mul_nonneg hq.le h2]
  have hcent : pairing (lineSum f) g ≤ c := by
    dsimp [c]
    rw [incidence_center]
    have hh : total f * total g ≤ 0 := by
      have hg : total g = -total f := by linarith only [hfg]
      rw [hg, mul_neg, ← pow_two]
      exact neg_nonpos.mpr (sq_nonneg _)
    have hd := div_nonpos_of_nonpos_of_nonneg hh hq.le
    linarith
  calc
    2*pairing (lineSum f) g ≤ 2*c := by linarith
    _ ≤ _ := he
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (energy_center_le f) (energy_center_le g)) hsqp.le

end CoboundaryExpanders.RankTwo

namespace CoboundaryExpanders.RankTwo
variable {K : Type} [Field K] [Fintype K]

omit [Fintype K] in
lemma edge_symm (x y : Vert K) : edge x y = edge y x := by
  cases x <;> cases y <;> rfl

attribute [local instance] OAI.CoboundaryExpanders.RankTwo.instDecidableEq_solutions_1
lemma point_degree (P : K×K) : EdgeMixing.mass edge (.inl P) = Fintype.card K := by
  simp only [EdgeMixing.mass,Fintype.sum_sum_type,edge,Finset.sum_const_zero,zero_add,
    Fintype.sum_prod_type]
  have he (a b : K) : P.2 = a*P.1+b ↔ b = P.2-a*P.1 := by
    constructor <;> intro h <;> linear_combination -h
  simp only [he]
  simp
lemma line_degree (L : K×K) : EdgeMixing.mass edge (.inr L) = Fintype.card K := by
  simp only [EdgeMixing.mass,Fintype.sum_sum_type,edge,Finset.sum_const_zero,add_zero,
    Fintype.sum_prod_type]
  simp
lemma edge_degree (v : Vert K) : EdgeMixing.mass edge v = Fintype.card K := by
  cases v with
  | inl P => exact point_degree P
  | inr L => exact line_degree L

lemma cross_pairing (f g : K → K → ℝ) :
    (∑ P : K×K, ∑ L : K×K,
      (if P.2 = L.1*P.1+L.2 then (1:ℝ) else 0)*f P.1 P.2*g L.1 L.2) =
      pairing (lineSum f) g := by
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]
  unfold pairing lineSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp

lemma edge_pairing (F : Vert K → ℝ) :
    EdgeMixing.pairing edge F F = 2 * pairing
      (lineSum (fun x y => F (.inl (x,y)))) (fun a b => F (.inr (a,b))) := by
  let f : K → K → ℝ := fun x y => F (.inl (x,y))
  let g : K → K → ℝ := fun x y => F (.inr (x,y))
  change _ = 2*pairing (lineSum f) g
  have hleft := cross_pairing f g
  have hright : (∑ L : K×K, ∑ P : K×K,
      (if P.2 = L.1*P.1+L.2 then (1:ℝ) else 0)*g L.1 L.2*f P.1 P.2) =
      pairing (lineSum f) g := by
    rw [Finset.sum_comm]
    convert hleft using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro P _
    apply Finset.sum_congr rfl
    intro L _
    ring
  simp only [EdgeMixing.pairing,Fintype.sum_sum_type,edge,zero_mul,Finset.sum_const_zero,
    zero_add,add_zero]
  change (∑ P : K×K, ∑ L : K×K,
    (if P.2=L.1*P.1+L.2 then (1:ℝ) else 0)*f P.1 P.2*g L.1 L.2) +
    (∑ L : K×K, ∑ P : K×K,
    (if P.2=L.1*P.1+L.2 then (1:ℝ) else 0)*g L.1 L.2*f P.1 P.2) = _
  rw [hleft,hright]
  ring

lemma edge_energy (F : Vert K → ℝ) : EdgeMixing.energy edge F =
    (Fintype.card K : ℝ) * (energy (fun x y => F (.inl (x,y))) +
      energy (fun x y => F (.inr (x,y)))) := by
  simp only [EdgeMixing.energy,edge_degree,Fintype.sum_sum_type,Fintype.sum_prod_type,
    ←Finset.mul_sum,energy]

lemma edge_mean (F : Vert K → ℝ) : (∑ v,EdgeMixing.mass edge v*F v) =
    (Fintype.card K : ℝ) * (total (fun x y => F (.inl (x,y))) +
      total (fun x y => F (.inr (x,y)))) := by
  simp only [edge_degree,Fintype.sum_sum_type,Fintype.sum_prod_type,←Finset.mul_sum,total]

theorem edge_rayleigh : EdgeMixing.Rayleigh (edge (K:=K))
    (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
  intro F hF
  have hq : (Fintype.card K : ℝ) ≠ 0 := ne_of_gt card_pos
  rw [edge_mean] at hF
  have hmean := (mul_eq_zero.mp hF).resolve_left hq
  rw [edge_pairing,edge_energy]
  have he := opposition_rayleigh (fun x y => F (.inl (x,y))) (fun x y => F (.inr (x,y))) hmean
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end CoboundaryExpanders.RankTwo

namespace CoboundaryExpanders.EdgeMixing
variable {V W : Type} [Fintype V] [Fintype W]

namespace Embedding
variable {e : V → V → ℝ} {d : W → W → ℝ} (M : Embedding e d)
  (hd : ∀ x y,d x y = d y x)
include M hd

omit hd [Fintype V] in
lemma mass_outside (y : W) (hy : y ∉ Set.range M.vertex) : mass d y = 0 := by
  simp only [mass,M.outside_zero y hy,Finset.sum_const_zero]
lemma mean_pull (F : W → ℝ) : (∑ y,mass d y*F y) = ∑ x,mass e x*F (M.vertex x) := by
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by rw [M.mass_outside y hy,zero_mul])]
  simp only [M.mass_map hd]
lemma energy_pull (F : W → ℝ) : energy d F = energy e (F ∘ M.vertex) := by
  unfold energy
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by rw [M.mass_outside y hy,zero_mul])]
  simp only [M.mass_map hd,Function.comp_apply]
lemma pairing_pull (F H : W → ℝ) : pairing d F H = pairing e (F ∘ M.vertex) (H ∘ M.vertex) := by
  unfold pairing
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by
    simp only [M.outside_zero y hy,zero_mul,Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by
    rw [hd,M.outside_zero y hy,zero_mul,zero_mul])]
  simp only [M.edge_eq,Function.comp_apply]

theorem push {lam : ℝ} (he : Rayleigh e lam) : Rayleigh d lam := by
  intro F hF
  rw [M.mean_pull hd] at hF
  rw [M.pairing_pull hd,M.energy_pull hd]
  exact he (F ∘ M.vertex) hF
end Embedding
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.InfiniteChains
namespace FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]

lemma cofaces_link (X : CoboundaryExpanders.InfiniteChains.Complex V) {N : ℕ} {s : Finset V} (hs : s ∈ X.faces)
    (hN : s.card ≤ N) {a : Finset V} (hd : Disjoint s a) :
    cofaces (X.faceLink s hs) (N-s.card) a = cofaces X N (s∪a) := by
  unfold cofaces
  apply Finset.card_bij (fun t _ => s∪t)
  · intro t ht
    obtain ⟨ht,hat⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    refine Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr ⟨ht.2,?_⟩,
      Finset.union_subset_union (Finset.Subset.refl _) hat⟩
    rw [Finset.card_union_of_disjoint ht.1,hcard]
    omega
  · intro t ht u hu he
    have hd1 := ((mem_level _ _ _).mp (Finset.mem_filter.mp ht).1).1.1
    have hd2 := ((mem_level _ _ _).mp (Finset.mem_filter.mp hu).1).1.1
    have hh := congrArg (fun t : Finset V => t\s) he
    simpa only [Finset.union_sdiff_cancel_left hd1,Finset.union_sdiff_cancel_left hd2] using hh
  · intro t ht
    obtain ⟨ht,hat⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    have hst : s ⊆ t := Finset.subset_union_left.trans hat
    have hdis : Disjoint s (t\s) := Finset.disjoint_left.mpr (fun v hv hv' => (Finset.mem_sdiff.mp hv').2 hv)
    refine ⟨t\s,Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr ⟨⟨hdis,?_⟩,?_⟩,?_⟩,?_⟩
    · rwa [Finset.union_sdiff_of_subset hst]
    · rw [Finset.card_sdiff_of_subset hst,hcard]
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hat (Finset.mem_union_right _ hv),fun h => Finset.disjoint_left.mp hd h hv⟩
    · exact Finset.union_sdiff_of_subset hst

lemma pure_link {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) {s : Finset V} (hs : s ∈ X.faces) :
    Pure (X.faceLink s hs) (N-s.card) := by
  have extension : ∀ a ∈ (X.faceLink s hs).faces,
      ∃ t ∈ level (X.faceLink s hs) (N-s.card), a ⊆ t := by
    intro a ha
    obtain ⟨t,ht,hat⟩ := hP.2 _ ha.2
    have ht' := (mem_level X N t).mp ht
    have hst := Finset.subset_union_left.trans hat
    refine ⟨t\s,(mem_level _ _ _).mpr ⟨⟨?_,?_⟩,?_⟩,?_⟩
    · exact Finset.disjoint_left.mpr (fun v hv hv' => (Finset.mem_sdiff.mp hv').2 hv)
    · rw [Finset.union_sdiff_of_subset hst]; exact ht'.1
    · rw [Finset.card_sdiff_of_subset hst,ht'.2]
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hat (Finset.mem_union_right _ hv), fun h => Finset.disjoint_left.mp ha.1 h hv⟩
  obtain ⟨t,ht,_⟩ := extension ∅ (X.faceLink s hs).empty_mem
  exact ⟨⟨t,ht⟩,extension⟩

end FiniteWeights

open FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

namespace FiniteWeights

lemma edge_symm (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (x y : V) : edge X N x y = edge X N y x := by
  simp only [edge,ne_comm,Finset.pair_comm]
lemma edge_nonneg (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (x y : V) : 0 ≤ edge X N x y := by
  unfold edge; split_ifs <;> positivity

lemma cofaces_pos {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) {s : Finset V} (hs : s ∈ X.faces) :
    0 < cofaces X N s := by
  obtain ⟨t,ht,hst⟩ := hP.2 s hs
  exact Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hst⟩⟩
lemma cofaces_pos_iff {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) (s : Finset V) :
    0 < cofaces X N s ↔ s ∈ X.faces := by
  refine ⟨fun h => ?_,cofaces_pos hP⟩
  by_contra hs
  rw [cofaces_zero_of_not_face X N hs] at h
  omega

end FiniteWeights

namespace Cone.FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

include M in
theorem rayleigh_push {N : ℕ} {lam : ℝ} (hX : EdgeMixing.Rayleigh (edge X N) lam) :
    EdgeMixing.Rayleigh (edge Y N) lam :=
  (M.spectralEmbedding N).push (edge_symm Y N) hX
end Cone.FaceModel
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.RankTwoGeometry
open InfiniteChains FiniteWeights MatrixOpposition
variable {K : Type} [Field K] [Fintype K]

attribute [local instance] OAI.CoboundaryExpanders.RankTwoGeometry.instDecidableEq_solutions_1
omit [Fintype K] in
lemma point_line_face (P L : K×K) :
    ({Sum.inl P,Sum.inr L}:Finset (Vert K)) ∈ (incidenceComplex K).faces ↔ incident P L := by
  constructor
  · rintro ⟨P',L',hPL,hs⟩
    have hP := hs (Finset.mem_insert_self _ _)
    have hL := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,false_or,or_false] at hP hL
    simpa only [hP,hL] using hPL
  · intro hPL
    exact ⟨P,L,hPL,Finset.Subset.refl _⟩
omit [Fintype K] in
lemma point_point_not_face (P Q : K×K) (hPQ : P ≠ Q) :
    ({Sum.inl P,Sum.inl Q}:Finset (Vert K)) ∉ (incidenceComplex K).faces := by
  rintro ⟨P',L',hPL,hs⟩
  have hP := hs (Finset.mem_insert_self _ _)
  have hQ := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inl.injEq,Sum.inl_ne_inr,or_false] at hP hQ
  exact hPQ (hP.trans hQ.symm)
omit [Fintype K] in
lemma line_line_not_face (L M : K×K) (hLM : L ≠ M) :
    ({Sum.inr L,Sum.inr M}:Finset (Vert K)) ∉ (incidenceComplex K).faces := by
  rintro ⟨P',L',hPL,hs⟩
  have hL := hs (Finset.mem_insert_self _ _)
  have hM := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inr.injEq,Sum.inr_ne_inl,false_or] at hL hM
  exact hLM (hL.trans hM.symm)

lemma incidence_edge (x y : Vert K) : edge (incidenceComplex K) 2 x y = RankTwo.edge x y := by
  cases x with
  | inl P =>
    cases y with
    | inl Q =>
      by_cases h : P = Q
      · subst Q; simp [edge,RankTwo.edge]
      · simp [edge,RankTwo.edge,h,cofaces_zero_of_not_face _ 2 (point_point_not_face P Q h)]
    | inr L =>
      rw [edge,ite_eq_left (by simp),cofaces_top _ 2 _ (by simp),point_line_face]
      simp only [RankTwo.edge,incident]
      split_ifs <;> simp_all
  | inr L =>
    cases y with
    | inl P =>
      rw [edge_symm,RankTwo.edge_symm]
      rw [edge,ite_eq_left (by simp),cofaces_top _ 2 _ (by simp),point_line_face]
      simp only [RankTwo.edge,incident]
      split_ifs <;> simp_all
    | inr M =>
      by_cases h : L = M
      · subst M; simp [edge,RankTwo.edge]
      · simp [edge,RankTwo.edge,h,cofaces_zero_of_not_face _ 2 (line_line_not_face L M h)]

theorem incidence_rayleigh : EdgeMixing.Rayleigh (edge (incidenceComplex K) 2)
    (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
  convert RankTwo.edge_rayleigh (K:=K) using 1
  all_goals try with_reducible_and_instances rfl
  funext x y
  exact incidence_edge x y

end CoboundaryExpanders.RankTwoGeometry

namespace CoboundaryExpanders.MatrixOpposition
open InfiniteChains FiniteWeights TypedCosetFaces
variable {K : Type} [Field K] [Fintype K]

theorem cut3_rayleigh : EdgeMixing.Rayleigh (edge (TypedCosetFaces.complex (cutGroups K 3)) 2)
    (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
  classical
  exact RankTwoGeometry.incidenceModel.rayleigh_push RankTwoGeometry.incidence_rayleigh
end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.EdgeMixing

section
variable {V W : Type} [Fintype V] [Fintype W]
attribute [local instance] Classical.propDecidable
namespace Embedding
variable {e : V → V → ℝ} {d : W → W → ℝ} (M : Embedding e d)
omit [Fintype W] in
lemma extend_map (f : V → ℝ) (x : V) : M.extend f (M.vertex x) = f x := by
  dsimp [extend]
  rw [dite_eq_left (show M.vertex x ∈ Set.range M.vertex from ⟨x,rfl⟩)]
  congr 1
  exact M.injective (Exists.choose_spec (show M.vertex x ∈ Set.range M.vertex from ⟨x,rfl⟩))
omit [Fintype W] in
lemma extend_comp (f : V → ℝ) : M.extend f ∘ M.vertex = f := funext (M.extend_map f)
include M in
theorem pull (hd : ∀ x y,d x y = d y x) {lam : ℝ} (h : Rayleigh d lam) : Rayleigh e lam := by
  intro f hf
  have hh := h (M.extend f) (by
    rw [M.mean_pull hd]
    simpa only [M.extend_map] using hf)
  rwa [M.pairing_pull hd,M.energy_pull hd,M.extend_comp] at hh
end Embedding

end

variable {A B : Type} [Fintype A] [Fintype B]

lemma bipartite_rayleigh : Rayleigh (bipartiteEdge (A:=A) (B:=B)) 0 := by
  intro f hf
  have hm : (Fintype.card B:ℝ)*(∑a,f (Sum.inl a))+(Fintype.card A:ℝ)*(∑b,f (Sum.inr b)) = 0 := by
    simpa only [Fintype.sum_sum_type,bipartite_mass_left,bipartite_mass_right,←Finset.mul_sum] using hf
  have hp : pairing bipartiteEdge f f = 2*(∑a,f (Sum.inl a))*(∑b,f (Sum.inr b)) := by
    simp only [pairing,Fintype.sum_sum_type,bipartiteEdge,zero_mul,one_mul,
      Finset.sum_const_zero,zero_add,add_zero,←Finset.mul_sum,←Finset.sum_mul]
    ring
  rw [hp,zero_mul]
  by_cases ha : IsEmpty A
  · let := ha
    simp
  · have han : 0 < (Fintype.card A:ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr (not_isEmpty_iff.mp ha)
    have hmult := congrArg (fun r : ℝ => r*(∑a,f (Sum.inl a))) hm
    have hsq := mul_nonneg (Nat.cast_nonneg (Fintype.card B) : (0:ℝ) ≤ _) (sq_nonneg (∑a,f (Sum.inl a)))
    have hprod : (∑a,f (Sum.inl a))*(∑b,f (Sum.inr b)) ≤ 0 := by
      apply (mul_le_mul_iff_right₀ han).mp
      change (Fintype.card A:ℝ)*((∑a,f (Sum.inl a))*(∑b,f (Sum.inr b))) ≤ (Fintype.card A:ℝ)*0
      nlinarith [hmult,hsq]
    linarith
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.InfiniteChains.Join
open Cone FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

lemma rankOne_rayleigh {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W}
    (hX : RankBound X 1) (hY : RankBound Y 1) : EdgeMixing.Rayleigh (edge (complex X Y) 2) 0 :=
  (rankOneEmbedding hX hY).push (edge_symm _ _) EdgeMixing.bipartite_rayleigh
end CoboundaryExpanders.InfiniteChains.Join

namespace CoboundaryExpanders.EdgeMixing
variable {V : Type} [Fintype V]
lemma rayleigh_mono {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) {a b : ℝ}
    (h : Rayleigh e a) (hab : a ≤ b) : Rayleigh e b := by
  intro f hf
  apply (h f hf).trans
  apply mul_le_mul_of_nonneg_right hab
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (Finset.sum_nonneg (fun y _ => he x y)) (sq_nonneg _))
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.InfiniteChains
open Cone FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

lemma Cone.FaceModel.rayleigh_pull {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    (N : ℕ) {lam : ℝ} (hY : EdgeMixing.Rayleigh (edge Y N) lam) :
    EdgeMixing.Rayleigh (edge X N) lam :=
  (M.spectralEmbedding N).pull (edge_symm Y N) hY

lemma Cone.FaceModel.pushTopSpectral {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N : ℕ} {lam : ℝ} (h : TopSpectral X N lam) : TopSpectral Y N lam := by
  intro t ht hn
  obtain ⟨s,hs,rfl⟩ := M.cover t ht
  rw [Finset.card_image_of_injective _ M.injective] at hn
  exact (M.linkModel s hs).rayleigh_push (h s hs hn)
lemma Cone.FaceModel.pullTopSpectral {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N : ℕ} {lam : ℝ} (h : TopSpectral Y N lam) : TopSpectral X N lam := by
  intro s hs hn
  apply (M.linkModel s hs).rayleigh_pull 2
  apply h
  rwa [Finset.card_image_of_injective _ M.injective]

theorem Join.topSpectral {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} {A B : ℕ} {lam : ℝ}
    (hX : RankBound X A) (hY : RankBound Y B) (h0 : 0 ≤ lam)
    (hTX : TopSpectral X A lam) (hTY : TopSpectral Y B lam) :
    TopSpectral (Join.complex X Y) (A+B) lam := by
  intro s hs hn
  have hL := hX s.toLeft hs.1
  have hR := hY s.toRight hs.2
  have hC := Finset.card_toLeft_add_card_toRight (u:=s)
  rw [Join.link_eq hs]
  by_cases hA : s.toLeft.card = A
  · have hB : s.toRight.card+2 = B := by omega
    exact (Join.emptyLeftModel (hX.terminal hs.1 hA)).rayleigh_push (hTY _ hs.2 hB)
  by_cases hB : s.toRight.card = B
  · have hAl : s.toLeft.card+2 = A := by omega
    exact (Join.emptyRightModel (hY.terminal hs.2 hB)).rayleigh_push (hTX _ hs.1 hAl)
  have hAl : A-s.toLeft.card = 1 := by omega
  have hBl : B-s.toRight.card = 1 := by omega
  apply EdgeMixing.rayleigh_mono (edge_nonneg _ _) _ h0
  exact Join.rankOne_rayleigh (hAl ▸ hX.link hs.1) (hBl ▸ hY.link hs.2)

lemma TopSpectral.vertexCriterion {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} {lam : ℝ}
    (hBase : N = 2 → EdgeMixing.Rayleigh (edge X 2) lam)
    (hVertex : ∀ v : V, ∀ hv : {v} ∈ X.faces, TopSpectral (X.faceLink {v} hv) (N-1) lam) :
    TopSpectral X N lam := by
  intro s hs hn
  by_cases he : s = ∅
  · subst s
    simpa only [faceLink_empty] using hBase (by simpa using hn.symm)
  obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hvx : {v} ∈ X.faces := X.downward hs (Finset.singleton_subset_iff.mpr hv)
  have hu : {v} ∪ s.erase v = s := by simp [Finset.insert_erase hv]
  have ht : s.erase v ∈ (X.faceLink {v} hvx).faces := by
    constructor
    · simp
    · rwa [hu]
  have hc : (s.erase v).card = s.card-1 := Finset.card_erase_of_mem hv
  have hp := Finset.card_pos.mpr ⟨v,hv⟩
  have HH := hVertex v hvx (s.erase v) ht (by omega)
  rw [faceLink_iterated] at HH
  have heq : X.faceLink ({v} ∪ s.erase v) ht.2 = X.faceLink s hs := by
    apply complex_eq
    ext a
    simp only [Complex.faceLink, hu]
  rwa [heq] at HH
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag TypedCosetFaces InfiniteChains Cone
open scoped Pointwise
variable {K : Type} [Field K] {N : ℕ}
lemma cut_middle_topSpectral [Fintype K] {a b : ℕ} {lam : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h0 : 0 ≤ lam)
    (hA : TopSpectral (TypedCosetFaces.complex (cutGroups K a)) (a-1) lam)
    (hB : TopSpectral (TypedCosetFaces.complex (cutGroups K b)) (b-1) lam) :
    TopSpectral (linkComplex (cutGroups K (a+b)) {middleCut ha hb}) ((a-1)+(b-1)) lam := by
  classical
  let : Fintype (Vertex (productGroups (cutGroups K a) (cutGroups K b))) := Fintype.ofFinite _
  let : Fintype (Vertex (vertexLinkGroups (cutGroups K (a+b)) (middleCut ha hb))) := Fintype.ofFinite _
  have hj := Join.topSpectral cut_rankBound cut_rankBound h0 hA hB
  exact (singleLinkModel _ _).pushTopSpectral
    ((cutProductLinkModel ha hb).pushTopSpectral
      ((productModel (cutGroups K a) (cutGroups K b)).pullTopSpectral hj))

theorem cut_topSpectral [Fintype K] (N : ℕ) :
    TopSpectral (TypedCosetFaces.complex (cutGroups K N)) (N-1)
      (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
  classical
  induction N using Nat.strong_induction_on with | h N ih =>
  apply TopSpectral.vertexCriterion
  · intro hbase
    have hN : N = 3 := by omega
    subst N
    exact cut3_rayleigh
  intro v hv
  rcases v with ⟨c,v⟩
  induction v using Quotient.inductionOn with | h g =>
  have hstandard : TopSpectral (linkComplex (cutGroups K N) {c}) (N-1-1)
      (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
    rcases c with ⟨a,ha,haN⟩
    obtain ⟨b,hNb⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt haN)
    subst N
    have hb : 0 < b := by omega
    have hbN : b < a+b := by omega
    have hc := cut_middle_topSpectral ha hb (by positivity)
      (ih a haN) (ih b hbN)
    have he : (a-1)+(b-1) = a+b-1-1 := by omega
    rwa [he] at hc
  rw [standard_link_eq] at hstandard
  have hm := (actionModel (cutGroups K N) g).linkModel {vertex (cutGroups K N) 1 c}
    (standard_singleton_face _ _)
  have hh := hm.pushTopSpectral hstandard
  have he : (actionModel (cutGroups K N) g).vertex (vertex (cutGroups K N) 1 c) =
      vertex (cutGroups K N) g c := by
    change g • vertex (cutGroups K N) 1 c = _
    rw [smul_vertex,mul_one]
  have hi : ({vertex (cutGroups K N) 1 c} : Finset _).image
      (actionModel (cutGroups K N) g).vertex = {vertex (cutGroups K N) g c} := by
    rw [Finset.image_singleton,he]

  rw [faceLink_congr _ hv hi] at hh
  exact hh

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)
  [Fintype (Vertex H)]
lemma allVertexTopSpectral_of_standard {N : ℕ} {lam : ℝ}
    (hs : ∀ i : I, TopSpectral (linkComplex H {i}) N lam) :
    ∀ v : Vertex H, ∀ hv : {v} ∈ (complex H).faces,
      TopSpectral ((complex H).faceLink {v} hv) N lam := by
  rintro ⟨i,v⟩ hv
  induction v using Quotient.inductionOn with | h g =>
  have hh := hs i
  rw [standard_link_eq] at hh
  have hh' := ((actionModel H g).linkModel {vertex H 1 i} (standard_singleton_face H i)).pushTopSpectral hh
  have he : (actionModel H g).vertex (vertex H 1 i) = vertex H g i := by
    change g • vertex H 1 i = _
    rw [smul_vertex,mul_one]
  have hi : ({vertex H 1 i} : Finset _).image (actionModel H g).vertex = {vertex H g i} := by
    rw [Finset.image_singleton,he]
  rw [faceLink_congr _ hv hi] at hh'
  exact hh'
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open InfiniteChains Cone TypedCosetFaces SphericalOpposition.CompleteFlag MatrixOpposition

attribute [local instance] OAI.CoboundaryExpanders.Construction.finiteFintype
theorem actual_topSpectral (n : ℕ) (hn : 2 ≤ n) (p : ℕ) [Fact p.Prime]
    (m : ℕ) (hm : 2 ≤ m) :
    TopSpectral (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1)
      (Real.sqrt (p:ℝ)/(p:ℝ)) := by
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  have hspherical := (cutSphericalModel (K:=ZMod p) (N:=n+1)).pushTopSpectral
    (cut_topSpectral (K:=ZMod p) (n+1))
  have hspherical' : TopSpectral (stdFlag (ZMod p) (n+1)).complex n
      (Real.sqrt (p:ℝ)/(p:ℝ)) := by
    simpa only [Nat.add_sub_cancel,ZMod.card] using hspherical
  apply TopSpectral.vertexCriterion
  · omega
  apply allVertexTopSpectral_of_standard
  intro cut
  have hc := (sphericalLinkModel p n (by omega) hm cut).pullTopSpectral hspherical'
  have ha := (actualVertexLinkModel p n (by omega) m cut).pushTopSpectral hc
  simpa only [Nat.add_sub_cancel] using ha
end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Averaging
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite F2 averaging and bounded-cone estimates for weighted local cochains.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Averaging

section
open scoped BigOperators
variable {A B G : Type} [Fintype A] [Fintype B] [Fintype G]
  [DecidableEq A] [DecidableEq B] [DecidableEq G]

omit [DecidableEq A] in
lemma supportNorm_nonneg (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (f : A → ZMod 2) :
    0 ≤ supportNorm w f := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact le_rfl
  · exact hw a

omit [Fintype B] [DecidableEq B] in
lemma support_indicator_sum_le (s : Finset B) (f : B → ZMod 2) :
    (if ∑ b ∈ s, f b = 0 then (0 : ℝ) else 1) ≤
      ∑ b ∈ s, if f b = 0 then (0 : ℝ) else 1 := by
  split_ifs with h
  · exact Finset.sum_nonneg (fun b _ => by split_ifs <;> norm_num)
  · obtain ⟨b, hb, hfb⟩ : ∃ b ∈ s, f b ≠ 0 := by
      by_contra hh
      push Not at hh
      exact h (Finset.sum_eq_zero hh)
    calc
      (1 : ℝ) = (if f b = 0 then 0 else 1) := by simp [hfb]
      _ ≤ ∑ b ∈ s, if f b = 0 then (0 : ℝ) else 1 :=
        Finset.single_le_sum (f := fun b => if f b = 0 then (0 : ℝ) else 1)
          (fun b _ => by split_ifs <;> norm_num) hb

omit [DecidableEq G] in
lemma exists_le_of_sum_le [Nonempty G] (v : G → ℝ) (c : ℝ)
    (h : ∑ g, v g ≤ Fintype.card G * c) : ∃ g, v g ≤ c := by
  by_contra hn
  push Not at hn
  have hh : Fintype.card G * c < ∑ g, v g := by
    simpa using Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun g _ => hn g)
  linarith

omit [DecidableEq A] [DecidableEq G] in
theorem exists_small_dual [Nonempty G]
    (wA : A → ℝ) (hwA : ∀ a, 0 ≤ wA a) (hwSum : ∑ a, wA a = 1)
    (wB : B → ℝ) (hwB : ∀ b, 0 ≤ wB b)
    (act : G → B → B) (C : ℝ) (hC : 0 ≤ C)
    (H : A → Finset B) (R : ℕ) (hH : ∀ a, (H a).card ≤ R)
    (hOcc : ∀ a b, b ∈ H a → ∀ t, ((Finset.univ.filter (fun g => act g b = t)).card : ℝ) ≤
      Fintype.card G * C * wB t)
    (f : B → ZMod 2) :
    ∃ g, supportNorm wA (fun a => ∑ b ∈ H a, f (act g b)) ≤
      (R : ℝ) * C * supportNorm wB f := by
  apply exists_le_of_sum_le
  have hnon : 0 ≤ supportNorm wB f := supportNorm_nonneg wB hwB f
  have hp (a : A) (b : B) (hb : b ∈ H a) :
      ∑ g, (if f (act g b) = 0 then (0 : ℝ) else 1) ≤
        Fintype.card G * C * supportNorm wB f := by
    have he : (∑ g, if f (act g b) = 0 then (0 : ℝ) else 1) =
        ∑ t, ((Finset.univ.filter (fun g => act g b = t)).card : ℝ) *
          (if f t = 0 then (0 : ℝ) else 1) := by
      simp only [← Finset.sum_boole, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_eq_single (act g b)]
      · simp
      · intro t _ ht
        simp [ht.symm]
      · simp
    rw [he, supportNorm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    split_ifs with ht
    · simp
    · simpa using hOcc a b hb t
  calc
    (∑ g, supportNorm wA (fun a => ∑ b ∈ H a, f (act g b))) ≤
        ∑ g, ∑ a, wA a * ∑ b ∈ H a, if f (act g b) = 0 then (0 : ℝ) else 1 := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro a _
      have hh := mul_le_mul_of_nonneg_left (support_indicator_sum_le (H a) (fun b => f (act g b))) (hwA a)
      simpa only [mul_ite, mul_zero, mul_one] using hh
    _ = ∑ a, wA a * ∑ b ∈ H a, ∑ g, if f (act g b) = 0 then (0 : ℝ) else 1 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ∑ a, wA a * ((H a).card * (Fintype.card G * C * supportNorm wB f)) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hwA a)
      simpa using Finset.sum_le_sum (fun b (hb : b ∈ H a) => hp a b hb)
    _ ≤ ∑ a, wA a * ((R : ℝ) * (Fintype.card G * C * supportNorm wB f)) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hwA a)
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hH a)
      positivity
    _ = Fintype.card G * ((R : ℝ) * C * supportNorm wB f) := by
      rw [← Finset.sum_mul, hwSum]
      ring

end

open scoped BigOperators
variable {G A B : Type} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [DecidableEq G] [DecidableEq A] [DecidableEq B]
  [MulAction G A] [MulAction G B]

omit [Fintype G] [DecidableEq G] [DecidableEq A] in
lemma sum_smul (g : G) (f : A → ℝ) : (∑ a, f (g • a)) = ∑ a, f a := by
  exact (Equiv.sum_comp (MulAction.toPerm g) f)

omit [Fintype A] [DecidableEq G] [DecidableEq A] in
lemma action_average_eq (a b : A) (h : ∃ g : G, g • a = b) (f : A → ℝ) :
    (∑ g : G, f (g • a)) = ∑ g : G, f (g • b) := by
  obtain ⟨h, rfl⟩ := h
  simpa [mul_smul] using (Equiv.sum_comp (Equiv.mulRight h) (fun g : G => f (g • a))).symm

omit [DecidableEq G] [DecidableEq A] in
lemma transitive_average (a : A) (hTrans : ∀ b, ∃ g : G, g • a = b) (f : A → ℝ) :
    (Fintype.card A : ℝ) * (∑ g : G, f (g • a)) =
      Fintype.card G * ∑ b : A, f b := by
  calc
    (Fintype.card A : ℝ) * (∑ g : G, f (g • a)) = ∑ b : A, ∑ g : G, f (g • b) := by
      symm
      have h (b : A) := (action_average_eq a b (hTrans b) f).symm
      simp_rw [h]
      simp
    _ = ∑ g : G, ∑ b : A, f (g • b) := Finset.sum_comm
    _ = Fintype.card G * ∑ b : A, f b := by simp [sum_smul]

omit [Fintype B] [DecidableEq G] [DecidableEq A] in
theorem occupation_le_incidence (I : A → B → Prop) [DecidableRel I]
    (hI : ∀ (g : G) a b, I a b → I (g • a) (g • b))
    (hTrans : ∀ a a' : A, ∃ g : G, g • a = a')
    (b : B) (a : A) (hab : I a b) (t : B) :
    (Fintype.card A : ℝ) * ((Finset.univ.filter (fun g : G => g • b = t)).card : ℝ) ≤
      Fintype.card G * ((Finset.univ.filter (fun a : A => I a t)).card : ℝ) := by
  have hh : (∑ g : G, if g • b = t then (1 : ℝ) else 0) ≤
      ∑ g : G, if I (g • a) t then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro g _
    by_cases ht : g • b = t
    · have hi := hI g a b hab
      simp only [ht] at hi
      simp [ht, hi]
    · simp only [ht, ↓reduceIte]
      split_ifs <;> norm_num
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (Fintype.card A) : (0 : ℝ) ≤ _)
  rw [transitive_average a (hTrans a) (fun a => if I a t then (1 : ℝ) else 0)] at hh'
  simpa only [Finset.sum_boole] using hh'

end CoboundaryExpanders.Averaging

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
lemma eval_support (f : Finset V → k) (c : Raw V) :
    eval f c = ∑ s ∈ c.support, f s := by
  rw [eval, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hn : c s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have ho : c s = 1 := by
    have he : ∀ a : k, a = 0 ∨ a = 1 := by decide
    exact (he (c s)).resolve_left hn
  simp [ho]

lemma eval_delta (f : Finset V → k) (c : Raw V) :
    eval (delta f) c = eval f (rawBoundary c) := by
  have hh : eval (delta f) = (eval f).comp rawBoundary := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, eval_single]
    have hsingle : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
    rw [hsingle, map_smul, map_smul]
    rfl
  exact LinearMap.congr_fun hh c

@[simp] lemma delta_delta (f : Finset V → k) (s : Finset V) : delta (delta f) s = 0 := by
  rw [delta, eval_delta]
  change eval f ((rawBoundary.comp rawBoundary) (Finsupp.single s 1)) = 0
  rw [rawBoundary_squared]
  simp

omit [DecidableEq V] in
lemma eval_correction (T : Raw V →ₗ[k] Raw V) (f : Finset V → k) (c : Raw V) :
    eval (correction T f) c = eval f (T c) := by
  have hh : eval (correction T f) = (eval f).comp T := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, eval_single]
    have hsingle : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
    rw [hsingle, map_smul, map_smul]
    rfl
  exact LinearMap.congr_fun hh c

lemma correction_identity {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (f : Finset V → k) (s : Finset V) (hs : s ∈ X.faces) (hn : s.card ≤ n) :
    f s + delta (correction H.hom f) s = eval (delta f) (H.hom (Finsupp.single s 1)) := by
  have hh := congrArg (eval f) (H.contraction s hs hn)
  rw [map_add, eval_single, one_mul, ← eval_delta f (H.hom (Finsupp.single s 1)),
    ← eval_correction H.hom f (rawBoundary (Finsupp.single s 1))] at hh
  change _ + delta (correction H.hom f) s = f s at hh
  rw [← hh]
  simp [add_assoc, CharTwo.add_self_eq_zero]

variable {G : Type} [Group G] [MulAction G V]
open scoped Pointwise

lemma eval_pull (g : G) (f : Finset V → k) (c : Raw V) :
    eval (pull g f) c = eval f (relabel (fun v => g • v) c) := by
  have hh : eval (pull g f) = (eval f).comp (relabel (fun v => g • v)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp [pull, Finset.image_smul]
  exact LinearMap.congr_fun hh c

lemma delta_pull (g : G) (f : Finset V → k) (s : Finset V) :
    delta (pull g f) s = pull g (delta f) s := by
  rw [delta, eval_pull]
  have hh := LinearMap.congr_fun (relabel_boundary (fun v : V => g • v)
    (MulAction.injective g)) (Finsupp.single s 1)
  simp only [LinearMap.comp_apply, relabel_single, Finset.image_smul] at hh
  rw [← hh]
  rfl

lemma movedCorrection_identity {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (g : G) (f : Finset V → k) (s : Finset V) (hs : s ∈ X.faces) (hn : s.card ≤ n) :
    f (g • s) + delta (movedCorrection g H.hom f) (g • s) =
      ∑ t ∈ (H.hom (Finsupp.single s 1)).support, delta f (g • t) := by
  have hh := correction_identity H (pull g f) s hs hn
  have he : delta (movedCorrection g H.hom f) (g • s) =
      delta (correction H.hom (pull g f)) s := by
    rw [movedCorrection, delta_pull]
    simp [pull]
  rw [he]
  simpa only [pull, funext (delta_pull g f), eval_support] using hh

end CoboundaryExpanders.InfiniteChains.Cone

namespace CoboundaryExpanders.InfiniteChains.FiniteWeights

section
open Attachment Cone Averaging
open scoped BigOperators Pointwise
variable {V : Type} [Fintype V] [DecidableEq V]

lemma weight_nonneg (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) (s : Finset V) : 0 ≤ weight X N r s := by
  unfold weight
  split_ifs <;> positivity

lemma cofaces_eq_sum (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (s : Finset V) :
    (cofaces X N s : ℝ) = ∑ t ∈ level X N, if s ⊆ t then (1 : ℝ) else 0 := by
  simp [cofaces]

lemma subsets_level (X : CoboundaryExpanders.InfiniteChains.Complex V) {N r : ℕ} (t : Finset V) (ht : t ∈ level X N) :
    (level X r).filter (fun s => s ⊆ t) = t.powersetCard r := by
  ext s
  simp only [Finset.mem_filter, mem_level, Finset.mem_powersetCard]
  constructor
  · intro h; exact ⟨h.2,h.1.2⟩
  · intro h; exact ⟨⟨X.downward (mem_level X N t |>.mp ht).1 h.1,h.2⟩,h.1⟩

lemma sum_cofaces (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) :
    (∑ s ∈ level X r, (cofaces X N s : ℝ)) =
      (N.choose r : ℝ) * (level X N).card := by
  simp_rw [cofaces_eq_sum]
  rw [Finset.sum_comm]
  have h (t : Finset V) (ht : t ∈ level X N) :
      (∑ s ∈ level X r, if s ⊆ t then (1 : ℝ) else 0) = N.choose r := by
    rw [Finset.sum_boole, subsets_level X t ht, Finset.card_powersetCard,
      (mem_level X N t).mp ht |>.2]
  rw [Finset.sum_congr rfl h]
  simp [mul_comm]

lemma weight_sum (X : CoboundaryExpanders.InfiniteChains.Complex V) {N r : ℕ} (hr : r ≤ N) (hN : (level X N).Nonempty) :
    ∑ s : Finset V, weight X N r s = 1 := by
  have hc : (N.choose r : ℝ) * (level X N).card ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne')
      (Nat.cast_ne_zero.mpr hN.card_pos.ne')
  simp only [weight, ← Finset.sum_filter]
  have he : Finset.univ.filter (fun s : Finset V => s ∈ level X r) = level X r := by ext; simp
  rw [he, ← Finset.sum_div, sum_cofaces, div_self hc]

variable {G : Type} [Group G] [Fintype G] [MulAction G V]

omit [Fintype V] [Fintype G] in
lemma invariant_iff {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (s : Finset V) :
    g • s ∈ X.faces ↔ s ∈ X.faces := by
  constructor
  · intro h
    simpa using hX g⁻¹ (g • s) h
  · exact hX g s

omit [Fintype G] in
lemma level_smul_iff {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (r : ℕ) (s : Finset V) :
    g • s ∈ level X r ↔ s ∈ level X r := by
  simp only [mem_level, invariant_iff hX, Finset.card_smul_finset]

omit [Fintype G] in
lemma cofaces_smul {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (N : ℕ) (s : Finset V) :
    cofaces X N (g • s) = cofaces X N s := by
  unfold cofaces
  symm
  apply Finset.card_bij (fun t _ => g • t)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨(level_smul_iff hX g N t).mpr (Finset.mem_filter.mp ht).1,
      Finset.smul_finset_subset_smul_finset (Finset.mem_filter.mp ht).2⟩
  · intro t ht u hu he
    exact MulAction.injective g he
  · intro t ht
    refine ⟨g⁻¹ • t, ?_, by simp⟩
    refine Finset.mem_filter.mpr ⟨(level_smul_iff hX g⁻¹ N t).mpr (Finset.mem_filter.mp ht).1, ?_⟩
    have hh := Finset.smul_finset_subset_smul_finset (a := g⁻¹) (Finset.mem_filter.mp ht).2
    simpa using hh

omit [Fintype G] in
lemma weight_smul {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (N r : ℕ) (s : Finset V) :
    weight X N r (g • s) = weight X N r s := by
  simp only [weight, level_smul_iff hX, cofaces_smul hX]

omit [Fintype G] in
lemma norm_pull {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (N r : ℕ) (f : Finset V → k) :
    supportNorm (weight X N r) (pull g f) = supportNorm (weight X N r) f := by
  classical
  unfold supportNorm
  apply Finset.sum_bij (fun s _ => g • s)
  · intro s hs; exact Finset.mem_univ _
  · intro s hs t ht he; exact MulAction.injective g he
  · intro s hs; exact ⟨g⁻¹ • s, Finset.mem_univ _, by simp⟩
  · intro s hs; simp only [pull, weight_smul hX]; rfl

end

open Attachment Cone Averaging
open scoped BigOperators Pointwise
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma card_faces (X : CoboundaryExpanders.InfiniteChains.Complex V) (r : ℕ) : Fintype.card (X.Face r) = (level X r).card := by
  let e : X.Face r ≃ ↥(level X r) :=
    { toFun := fun s => ⟨s.val, (mem_level X r s.val).mpr s.property⟩
      invFun := fun s => ⟨s.val,(mem_level X r s.val).mp s.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

lemma count_incident (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (s : Finset V) :
    (Finset.univ.filter (fun t : X.Face N => s ⊆ t.val)).card = cofaces X N s := by
  unfold cofaces
  apply Finset.card_bij (fun t _ => t.val)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨(mem_level X N t.val).mpr t.property,(Finset.mem_filter.mp ht).2⟩
  · intro t ht u hu he; exact Subtype.ext he
  · intro t ht
    refine ⟨⟨t,(mem_level X N t).mp (Finset.mem_filter.mp ht).1⟩,?_,rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp ht).2

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] [MulAction G V]

omit [DecidableEq G] in
lemma occupancy {X : CoboundaryExpanders.InfiniteChains.Complex V} {N r : ℕ} (hX : Invariant G X) (hP : Pure X N)
    (hTrans : ∀ a b : X.Face N, ∃ g : G, g • a.val = b.val)
    (hr : r ≤ N) (s : Finset V) (hs : s ∈ level X r) (t : Finset V) :
    ((Finset.univ.filter (fun g : G => g • s = t)).card : ℝ) ≤
      Fintype.card G * (N.choose r : ℝ) * weight X N r t := by
  classical
  by_cases ht : t ∈ level X r
  · obtain ⟨a,ha,hsa⟩ := hP.2 s ((mem_level X r s).mp hs).1
    let aa : X.Face N := ⟨a, (mem_level X N a).mp ha⟩
    let : MulAction G (X.Face N) := faceAction hX N
    have htrans : ∀ a b : X.Face N, ∃ g : G, g • a = b := by
      intro a b
      obtain ⟨g,hg⟩ := hTrans a b
      exact ⟨g, Subtype.ext hg⟩
    have hi : ∀ (g : G) (a : X.Face N) (b : Finset V), b ⊆ a.val →
        g • b ⊆ (g • a).val := by
      intro g a b hb
      exact Finset.smul_finset_subset_smul_finset hb
    have hh := occupation_le_incidence (fun a : X.Face N => fun b : Finset V => b ⊆ a.val)
      hi htrans s aa hsa t
    rw [card_faces, count_incident] at hh
    have hc : 0 < ((level X N).card : ℝ) := Nat.cast_pos.mpr hP.1.card_pos
    have hb : (N.choose r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
    rw [weight, ite_eq_left ht]
    apply le_of_mul_le_mul_left _ hc
    calc
      ((level X N).card : ℝ) * ((Finset.univ.filter (fun g : G => g • s = t)).card : ℝ) ≤
          Fintype.card G * (cofaces X N t : ℝ) := hh
      _ = (level X N).card * (Fintype.card G * (N.choose r : ℝ) *
          (cofaces X N t / ((N.choose r : ℝ) * (level X N).card))) := by
        field_simp
  · have hempty : Finset.univ.filter (fun g : G => g • s = t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have he := (Finset.mem_filter.mp hg).2
      have hmem := (level_smul_iff hX g r s).mpr hs
      exact ht (he ▸ hmem)
    simp [hempty, weight, ht]

omit [DecidableEq G] in
theorem weighted_correction {X : CoboundaryExpanders.InfiniteChains.Complex V} {N n r R : ℕ}
    (hX : Invariant G X) (hP : Pure X N)
    (hTrans : ∀ a b : X.Face N, ∃ g : G, g • a.val = b.val)
    (H : BoundedCone X n R) (hr : r ≤ n) (hrN : r+1 ≤ N)
    (f : Finset V → k) :
    ∃ b : Finset V → k,
      supportNorm (weight X N r) (fun s => f s + delta b s) ≤
        (R : ℝ) * (N.choose (r+1) : ℝ) * supportNorm (weight X N (r+1)) (delta f) := by
  classical
  let L : Finset V → Finset (Finset V) := fun s =>
    if s ∈ level X r then (H.hom (Finsupp.single s 1)).support else ∅
  have hL (s : Finset V) : (L s).card ≤ R := by
    dsimp only [L]
    split_ifs with hs
    · obtain ⟨hs',he⟩ := (mem_level X r s).mp hs
      exact H.bound s hs' (by omega)
    · simp
  have hLS (s t : Finset V) (ht : t ∈ L s) : t ∈ level X (r+1) := by
    dsimp only [L] at ht
    split_ifs at ht with hs
    · obtain ⟨hs',he⟩ := (mem_level X r s).mp hs
      have hh := ((mem_supported _ _).mp (H.support s hs' (by omega))) t (Finsupp.mem_support_iff.mp ht)
      exact (mem_level X (r+1) t).mpr ⟨hh.1, by simpa [he] using hh.2⟩
    · simp at ht
  obtain ⟨g,hg⟩ := exists_small_dual (G := G)
    (weight X N r) (weight_nonneg X N r) (weight_sum X (by omega) hP.1)
    (weight X N (r+1)) (weight_nonneg X N (r+1))
    (fun g t => g • t) (N.choose (r+1) : ℝ) (Nat.cast_nonneg _)
    L R hL (fun s t ht u => occupancy hX hP hTrans hrN t (hLS s t ht) u)
    (delta f)
  refine ⟨movedCorrection g H.hom f, ?_⟩
  rw [← norm_pull hX g]
  have he : supportNorm (weight X N r)
      (pull g (fun s => f s + delta (movedCorrection g H.hom f) s)) =
      supportNorm (weight X N r) (fun s => ∑ t ∈ L s, delta f (g • t)) := by
    unfold supportNorm
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ level X r
    · obtain ⟨hs',hsr⟩ := (mem_level X r s).mp hs
      have hh := movedCorrection_identity H g f s hs' (by omega)
      simp only [pull, L, ite_eq_left hs, hh]
    · simp [weight, hs]
  exact he ▸ hg

end CoboundaryExpanders.InfiniteChains.FiniteWeights

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite pure complexes, weighted F2 norms, distance to actual coboundaries, and the full main statement.
-/

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Complex

theorem weight_nonneg (X : Complex) (s i : ℕ) (σ : X.Face i) :
    0 ≤ X.weight s i σ := by
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem weight_pos {X : Complex} {s i : ℕ} (hX : X.Pure s) (hi : i ≤ s)
    (σ : X.Face i) : 0 < X.weight s i σ := by
  obtain ⟨τ, hτ, hστ⟩ := hX.2 σ.val (face_mem σ)
  have hn : 0 < ((X.facesOf s).filter (fun τ => σ.val ⊆ τ)).card :=
    Finset.card_pos.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, hστ⟩⟩
  exact div_pos (Nat.cast_pos.mpr hn)
    (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hi)))
      (Nat.cast_pos.mpr hX.1.card_pos))

attribute [local instance] OAI.CoboundaryExpanders.Complex.instFintypeFace_1
theorem norm_nonneg (X : Complex) (s i : ℕ) (f : X.Cochain i) :
    0 ≤ X.norm s i f := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact X.weight_nonneg s i σ
  · exact le_rfl

theorem norm_eq_zero_iff {X : Complex} {s i : ℕ} (hX : X.Pure s) (hi : i ≤ s)
    (f : X.Cochain i) : X.norm s i f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    ext σ
    change f σ = 0
    by_contra hσ
    have hle : X.weight s i σ ≤ X.norm s i f := by
      have := Finset.single_le_sum (f := fun ρ : X.Face i =>
        if f ρ ≠ 0 then X.weight s i ρ else 0)
        (fun ρ (_ : ρ ∈ Finset.univ) => by
          split_ifs
          · exact X.weight_nonneg s i ρ
          · exact le_rfl) (Finset.mem_univ σ)
      simpa only [norm, ite_eq_left hσ] using this
    exact (not_le_of_gt (weight_pos hX hi σ)) (hf ▸ hle)
  · rintro rfl
    exact X.norm_zero s i

theorem distance_attained (X : Complex) (s i : ℕ) (f : X.Cochain i)
    (A : Set (X.Cochain i)) (hA : A.Nonempty) :
    ∃ a ∈ A, X.distance s i f A = X.norm s i (f - a) := by
  have hfin : (((fun a => X.norm s i (f - a)) '' A) : Set ℝ).Finite :=
    (Set.toFinite A).image _
  obtain ⟨a, ha, heq⟩ := (hA.image (fun a => X.norm s i (f - a))).csInf_mem hfin
  exact ⟨a, ha, heq.symm⟩

theorem distance_le_norm (X : Complex) (s i : ℕ) (f : X.Cochain i)
    {A : Set (X.Cochain i)} {a : X.Cochain i} (ha : a ∈ A) :
    X.distance s i f A ≤ X.norm s i (f - a) := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨b, _, rfl⟩; exact X.norm_nonneg s i (f - b)⟩
  · exact ⟨a, ha, rfl⟩

theorem sum_face_eq {A : Type*} [AddCommMonoid A] (X : Complex) (i : ℕ)
    (g : Finset (Fin X.vertexCount) → A) :
    (∑ σ : X.Face i, g σ.val) = ∑ σ ∈ X.facesOf i, g σ :=
  (Finset.sum_subtype (X.facesOf i) (fun _ => Iff.rfl) g).symm

theorem cofaceCount_eq_sum (X : Complex) (s : ℕ) (σ : Finset (Fin X.vertexCount)) :
    X.cofaceCount s σ = ∑ τ : X.Face s, if σ ⊆ τ.val then (1 : ℕ) else 0 := by
  rw [sum_face_eq X s (fun τ => if σ ⊆ τ then (1 : ℕ) else 0), Finset.sum_boole]
  rfl

theorem sum_cofaceCount {X : Complex} {i s n : ℕ} (σ : X.Face i) (his : i ≤ s) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.cofaceCount n ρ.val else 0) =
    X.cofaceCount n σ.val * Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
  classical
  calc
    _ = ∑ ρ : X.Face s, ∑ τ : X.Face n,
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro ρ _
      by_cases h : σ.val ⊆ ρ.val <;> simp [h, cofaceCount_eq_sum]
    _ = ∑ τ : X.Face n, ∑ ρ : X.Face s,
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ τ : X.Face n, if σ.val ⊆ τ.val then
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) else 0 := by
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hστ : σ.val ⊆ τ.val
      · rw [ite_eq_left hστ, Finset.sum_boole]
        exact card_between_faces σ τ hστ his
      · rw [ite_eq_right hστ]
        apply Finset.sum_eq_zero
        intro ρ _
        exact ite_eq_right (fun h => hστ (h.1.trans h.2))
    _ = _ := by
      rw [cofaceCount_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs <;> simp

theorem sum_cofaceCount_real {X : Complex} {i s n : ℕ} (σ : X.Face i) (his : i ≤ s) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then (X.cofaceCount n ρ.val : ℝ) else 0) =
    (X.cofaceCount n σ.val : ℝ) * Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
  exact_mod_cast sum_cofaceCount (n := n) σ his

theorem facesOf_nonempty_of_pure {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) : (X.facesOf s).Nonempty := by
  obtain ⟨τ, hτ⟩ := hX.1
  have hτcard := ((mem_facesOf X n τ).mp hτ).2
  obtain ⟨σ, hστ, hσcard⟩ := Finset.exists_subset_card_eq
    (show s + 1 ≤ τ.card by omega)
  exact ⟨σ, (mem_facesOf X s σ).mpr
    ⟨X.downward ((mem_facesOf X n τ).mp hτ).1 hστ, hσcard⟩⟩

theorem weight_eq_cofaceCount (X : Complex) (n i : ℕ) (σ : X.Face i) :
    X.weight n i σ = (X.cofaceCount n σ.val : ℝ) /
      ((Nat.choose (n + 1) (i + 1) : ℝ) * (X.facesOf n).card) := rfl

theorem weight_averaging {X : Complex} {i s n : ℕ} (hX : (X.facesOf n).Nonempty)
    (his : i ≤ s) (hsn : s ≤ n) (σ : X.Face i) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight n s ρ else 0) =
      (Nat.choose (s + 1) (i + 1) : ℝ) * X.weight n i σ := by
  classical
  have hF : ((X.facesOf n).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hX.card_pos)
  have hAi : (Nat.choose (n + 1) (i + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ (his.trans hsn))))
  have hAs : (Nat.choose (n + 1) (s + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
  have hchoose :
      (Nat.choose (n + 1) (s + 1) : ℝ) * Nat.choose (s + 1) (i + 1) =
      (Nat.choose (n + 1) (i + 1) : ℝ) *
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
    exact_mod_cast Nat.choose_mul (n := n + 1) (Nat.succ_le_succ his)
  calc
    _ = (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then (X.cofaceCount n ρ.val : ℝ) else 0) /
        ((Nat.choose (n + 1) (s + 1) : ℝ) * (X.facesOf n).card) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ρ _
      split_ifs <;> simp [weight_eq_cofaceCount]
    _ = ((X.cofaceCount n σ.val : ℝ) *
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1))) /
        ((Nat.choose (n + 1) (s + 1) : ℝ) * (X.facesOf n).card) := by
      rw [sum_cofaceCount_real σ his]
    _ = _ := by
      rw [weight_eq_cofaceCount]
      field_simp
      linear_combination -(X.cofaceCount n σ.val : ℝ) * hchoose

@[simp] theorem weight_top {X : Complex} {s : ℕ} (σ : X.Face s) :
    X.weight s s σ = 1 / (X.facesOf s).card := by
  simp [weight_eq_cofaceCount]

theorem skeletonScale_pos {X : Complex} {n s : ℕ} (hX : X.Pure n) (hsn : s ≤ n) :
    0 < X.skeletonScale n s := by
  exact div_pos
    (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
      (Nat.cast_pos.mpr hX.1.card_pos))
    (Nat.cast_pos.mpr (facesOf_nonempty_of_pure hX hsn).card_pos)

theorem skeletonScale_mul_topweight {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) (ρ : X.Face s) :
    X.skeletonScale n s * X.weight n s ρ =
      (X.cofaceCount n ρ.val : ℝ) * X.weight s s ρ := by
  have hCount : ((X.facesOf n).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hX.1.card_pos)
  have hChoose : (Nat.choose (n + 1) (s + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
  rw [skeletonScale, weight_eq_cofaceCount, weight_top]
  field_simp

theorem skeleton_topweight_comparison {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (ρ : X.Face s) :
    (X.skeletonScale n s / b) * X.weight n s ρ ≤ X.weight s s ρ ∧
      X.weight s s ρ ≤ (X.skeletonScale n s / a) * X.weight n s ρ := by
  have heq := skeletonScale_mul_topweight hX hsn ρ
  have hw := X.weight_nonneg s s ρ
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hb, heq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hcount ρ).2 hw
  · rw [div_mul_eq_mul_div, le_div_iff₀ ha, heq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hcount ρ).1 hw

theorem skeleton_weight_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (σ : X.Face i) :
    (X.skeletonScale n s / b) * X.weight n i σ ≤ X.weight s i σ ∧
      X.weight s i σ ≤ (X.skeletonScale n s / a) * X.weight n i σ := by
  classical
  have hXs := facesOf_nonempty_of_pure hX hsn
  obtain ⟨ρ₀, hρ₀⟩ := facesOf_nonempty_of_pure hX hsn
  have hb : 0 < b := (ha.trans_le (hcount ⟨ρ₀, hρ₀⟩).1).trans_le
    (hcount ⟨ρ₀, hρ₀⟩).2
  have hB : (0 : ℝ) < Nat.choose (s + 1) (i + 1) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ his))
  have sum_scaled (c : ℝ) (t : ℕ) :
      (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then c * X.weight t s ρ else 0) =
      c * ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight t s ρ else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  constructor
  · have hlo :
        (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then
          (X.skeletonScale n s / b) * X.weight n s ρ else 0) ≤
        ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight s s ρ else 0 := by
      apply Finset.sum_le_sum
      intro ρ _
      split_ifs
      · exact (skeleton_topweight_comparison hX hsn ha hb hcount ρ).1
      · exact le_rfl
    rw [sum_scaled, weight_averaging hX.1 his hsn σ,
      weight_averaging hXs his le_rfl σ] at hlo
    apply (mul_le_mul_iff_right₀ hB).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hlo
  · have hhi :
        (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight s s ρ else 0) ≤
        ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then
          (X.skeletonScale n s / a) * X.weight n s ρ else 0 := by
      apply Finset.sum_le_sum
      intro ρ _
      split_ifs
      · exact (skeleton_topweight_comparison hX hsn ha hb hcount ρ).2
      · exact le_rfl
    rw [sum_scaled, weight_averaging hX.1 his hsn σ,
      weight_averaging hXs his le_rfl σ] at hhi
    apply (mul_le_mul_iff_right₀ hB).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hhi

theorem norm_le_of_weight_le {X : Complex} {r s i : ℕ} {c : ℝ}
    (hw : ∀ σ : X.Face i, X.weight r i σ ≤ c * X.weight s i σ)
    (f : X.Cochain i) : X.norm r i f ≤ c * X.norm s i f := by
  rw [norm, norm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  split_ifs
  · exact hw σ
  · simp

theorem distance_le_of_weight_le {X : Complex} {r s i : ℕ} {c : ℝ}
    (hw : ∀ σ : X.Face i, X.weight r i σ ≤ c * X.weight s i σ)
    (f : X.Cochain i) {A : Set (X.Cochain i)} (hA : A.Nonempty) :
    X.distance r i f A ≤ c * X.distance s i f A := by
  obtain ⟨a, ha, heq⟩ := X.distance_attained s i f A hA
  rw [heq]
  exact (X.distance_le_norm r i f ha).trans (norm_le_of_weight_le hw (f - a))

theorem skeleton_norm_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (f : X.Cochain i) :
    (X.skeletonScale n s / b) * X.norm n i f ≤ X.norm s i f ∧
      X.norm s i f ≤ (X.skeletonScale n s / a) * X.norm n i f := by
  constructor
  · rw [norm, norm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    split_ifs
    · exact (skeleton_weight_comparison hX his hsn ha hcount σ).1
    · simp
  · exact norm_le_of_weight_le
      (fun σ => (skeleton_weight_comparison hX his hsn ha hcount σ).2) f

theorem skeleton_distance_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (f : X.Cochain i) {A : Set (X.Cochain i)} (hA : A.Nonempty) :
    (X.skeletonScale n s / b) * X.distance n i f A ≤ X.distance s i f A ∧
      X.distance s i f A ≤ (X.skeletonScale n s / a) * X.distance n i f A := by
  obtain ⟨ρ₀, hρ₀⟩ := facesOf_nonempty_of_pure hX hsn
  have hb : 0 < b := (ha.trans_le (hcount ⟨ρ₀, hρ₀⟩).1).trans_le
    (hcount ⟨ρ₀, hρ₀⟩).2
  constructor
  · obtain ⟨a₀, ha₀, heq⟩ := X.distance_attained s i f A hA
    rw [heq]
    exact (mul_le_mul_of_nonneg_left (X.distance_le_norm n i f ha₀)
      (le_of_lt (div_pos (skeletonScale_pos hX hsn) hb))).trans
      (skeleton_norm_comparison hX his hsn ha hcount (f - a₀)).1
  · exact distance_le_of_weight_le
      (fun σ => (skeleton_weight_comparison hX his hsn ha hcount σ).2) f hA

end CoboundaryExpanders.Complex

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_FatLadders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Balanced chamber weights, fat ladders, degeneracy, and cochain counting.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.FatLadders

section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

namespace Path
variable {F : Finset V → Prop} {s a : Finset V}
lemma fat (h : Path F s a) : F a := by cases h with | refl h => exact h | step _ _ _ h => exact h
lemma subset (h : Path F s a) : s ⊆ a := by
  induction h with
  | refl _ => exact Finset.Subset.refl _
  | step v _ _ _ ih => exact ih.trans (Finset.subset_insert _ _)
end Path

lemma Path.erase_fat {F : Finset V → Prop} {s a T : Finset V}
    (h : Path F s a) (hT : a ⊆ T) (hn : NoBad F T) (x : V) (hx : x ∈ s)
    (he : F (a.erase x)) : F (s.erase x) := by
  induction h with
  | refl _ => exact he
  | @step b v hb hv hf ih =>
    have hxb : x ∈ b := hb.subset hx
    have hvx : v ≠ x := by intro e; subst v; exact hv hxb
    have hfb : F b := hb.fat
    have hsmall : F (b.erase x) := by
      have hh := hn (insert v b) hT v (Finset.mem_insert_self _ _) x
        (Finset.mem_insert_of_mem hxb) hvx (by simpa [Finset.erase_insert hv] using hfb) he
      simpa only [Finset.erase_insert hv] using hh
    exact ih ((Finset.subset_insert v b).trans hT) hsmall

lemma Path.erase_path {F : Finset V → Prop} {s a T : Finset V}
    (h : Path F s a) (hT : a ⊆ T) (hn : NoBad F T) (x : V) (hx : x ∉ s)
    (he : F (a.erase x)) : Path F s (a.erase x) := by
  induction h with
  | refl hf => simpa [Finset.erase_eq_of_notMem hx] using Path.refl hf
  | @step b v hb hv hf ih =>
    by_cases hvx : v = x
    · subst v
      simpa only [Finset.erase_insert hv] using hb
    · by_cases hxb : x ∈ b
      · have hsmall : F (b.erase x) := by
          have hh := hn (insert v b) hT v (Finset.mem_insert_self _ _) x
            (Finset.mem_insert_of_mem hxb) hvx
            (by simpa only [Finset.erase_insert hv] using hb.fat) he
          simpa only [Finset.erase_insert hv] using hh
        have hp := ih ((Finset.subset_insert v b).trans hT) hsmall
        have hv' : v ∉ b.erase x := fun hh => hv (Finset.mem_of_mem_erase hh)
        rw [Finset.erase_insert_of_ne hvx]
        exact Path.step v hp hv' (by simpa only [Finset.erase_insert_of_ne hvx] using he)
      · have hnot : x ∉ insert v b := by simp [hxb,Ne.symm hvx]
        simpa only [Finset.erase_eq_of_notMem hnot] using Path.step v hb hv hf

theorem exchange {F : Finset V → Prop} {s T : Finset V} (hs : Minimal F s)
    (hn : NoBad F T) {x y : V} (hx : x ∈ T) (hy : y ∈ T)
    (hp : Path F s (T.erase x)) (hf : F (T.erase y)) :
    Path F s (T.erase y) := by
  by_cases hxy : x = y
  · simpa only [hxy] using hp
  have he : F ((T.erase x).erase y) := hn T (Finset.Subset.refl _) x hx y hy hxy hp.fat hf
  have hys : y ∉ s := by
    intro h
    exact hs.2 y h (hp.erase_fat (Finset.erase_subset _ _) hn y h he)
  have hr := hp.erase_path (Finset.erase_subset _ _) hn y hys he
  have hxi : x ∉ (T.erase x).erase y := by simp
  have hrep : insert x ((T.erase x).erase y) = T.erase y := by
    rw [Finset.erase_right_comm,Finset.insert_erase]
    exact Finset.mem_erase.mpr ⟨hxy,hx⟩
  rw [← hrep]
  exact Path.step x hr hxi (hrep ▸ hf)

theorem localized_boundary_support {F : Finset V → Prop} {s T : Finset V}
    (hs : Minimal F s) (hn : NoBad F T)
    (hb : delta (indicator (Path F s)) T ≠ 0) :
    delta (indicator F) T ≠ 0 := by
  have hex : ∃ x ∈ T, Path F s (T.erase x) := by
    by_contra h
    push Not at h
    apply hb
    apply Finset.sum_eq_zero
    intro x hx
    simp only [indicator,ite_eq_right (h x hx)]
  obtain ⟨x,hx,hp⟩ := hex
  have he : delta (indicator (Path F s)) T = delta (indicator F) T := by
    apply Finset.sum_congr rfl
    intro y hy
    apply congrArg (fun b : Prop => if b then (1:k) else 0)
    apply propext
    exact ⟨Path.fat, fun hf => exchange hs hn hx hy hp hf⟩
  rwa [← he]

lemma indicator_vanish {F : Finset V → Prop} {s a : Finset V} (h : ¬ s ⊆ a) :
    indicator (Path F s) a = 0 := by
  exact ite_eq_right (fun hp => h hp.subset)

theorem exists_minimal_path (F : Finset V → Prop) (a : Finset V) (ha : F a) :
    ∃ s ⊆ a, Minimal F s ∧ Path F s a := by
  induction a using Finset.strongInductionOn with
  | _ a ih =>
    by_cases h : ∃ x ∈ a, F (a.erase x)
    · obtain ⟨x,hx,hf⟩ := h
      obtain ⟨s,hs,hm,hp⟩ := ih (a.erase x) (Finset.erase_ssubset hx) hf
      refine ⟨s,hs.trans (Finset.erase_subset _ _),hm,?_⟩
      have he : insert x (a.erase x) = a := Finset.insert_erase hx
      have hf' : F (insert x (a.erase x)) := by rwa [he]
      simpa only [he] using Path.step x hp (Finset.notMem_erase _ _) hf'
    · refine ⟨a,Finset.Subset.refl _,⟨ha,?_⟩,Path.refl ha⟩
      intro x hx hf
      exact h ⟨x,hx,hf⟩

lemma minimal_nonempty {F : Finset V → Prop} (hF : ¬ F ∅) {s : Finset V}
    (hs : Minimal F s) : s.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  subst s
  exact hF hs.1

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma starNorm_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r s) (f : Finset V → k) :
    0 ≤ starNorm w r s f := by
  apply Finset.sum_nonneg
  intro t ht
  split_ifs
  · exact atom_nonneg hw f t
  · exact le_rfl

lemma starNorm_add_le {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r s) (f g : Finset V → k) :
    starNorm w r s (f+g) ≤ starNorm w r s f + starNorm w r s g := by
  rw [starNorm,starNorm,starNorm,starSum,starSum,starSum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  split_ifs
  · exact atom_add_le hw f g t
  · simp

lemma starSum_mono {r : ℕ} {s : Finset V} {f g : Finset V → ℝ}
    (h : ∀ t ∈ level r, s ⊆ t → f t ≤ g t) : starSum r s f ≤ starSum r s g := by
  apply Finset.sum_le_sum
  intro t ht
  split_ifs with hs
  · exact h t ht hs
  · rfl

omit [Fintype V] in
lemma subsets_card_le (S : Finset (Finset V)) (t : Finset V) :
    (S.filter (fun s => s ⊆ t)).card ≤ 2^t.card := by
  rw [← Finset.card_powerset]
  exact Finset.card_le_card (by intro s hs; exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hs).2)

lemma sum_star_le (S : Finset (Finset V)) (r : ℕ) (f : Finset V → ℝ)
    (hf : ∀ t, 0 ≤ f t) :
    (∑ s ∈ S, starSum r s f) ≤ (2:ℝ)^r * ∑ t ∈ level r, f t := by
  unfold starSum
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have he : (∑ s ∈ S, if s ⊆ t then f t else 0) =
      ((S.filter (fun s => s ⊆ t)).card : ℝ) * f t := by
    rw [← Finset.sum_filter]
    simp
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (hf t)
  have hh := subsets_card_le S t
  have hr := mem_level.mp ht
  rw [hr] at hh
  exact_mod_cast hh

omit [Fintype V] in
lemma ladder_difference (w : Finset V → ℝ) (F : Finset V → Prop) (s t : Finset V) :
    atom w (indicator F + indicator (Path F s)) t =
      atom w (indicator F) t - atom w (indicator (Path F s)) t := by
  by_cases hp : Path F s t
  · have hf := hp.fat
    simp [atom,indicator,hp,hf,CharTwo.add_self_eq_zero]
  · by_cases hf : F t <;> simp [atom,indicator,hp,hf]

lemma ladder_star_difference (w : Finset V → ℝ) (F : Finset V → Prop) (r) (s : Finset V) :
    starNorm w r s (indicator F + indicator (Path F s)) =
      starNorm w r s (indicator F) - starNorm w r s (indicator (Path F s)) := by
  unfold starNorm starSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs
  · exact ladder_difference w F s t
  · ring

lemma norm_le_ladders {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (F : Finset V → Prop) (r : ℕ) :
    norm w r (indicator F) ≤ ∑ s ∈ minimalFaces F, starNorm w r s (indicator (Path F s)) := by
  unfold norm starNorm starSum
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hF : F t
  · obtain ⟨s,hst,hs,hp⟩ := exists_minimal_path F t hF
    have hmem : s ∈ minimalFaces F := by simp [minimalFaces,hs]
    calc
      atom w (indicator F) t =
          (if s ⊆ t then atom w (indicator (Path F s)) t else 0) := by simp [atom,indicator,hF,hp,hst]
      _ ≤ ∑ a ∈ minimalFaces F, if a ⊆ t then atom w (indicator (Path F a)) t else 0 := by
        apply Finset.single_le_sum _ hmem
        intro a ha
        split_ifs
        · exact atom_nonneg hw _ _
        · exact le_rfl
  · have hh : atom w (indicator F) t = 0 := by simp [atom,indicator,hF]
    rw [hh]
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact atom_nonneg hw _ _
    · exact le_rfl

lemma ladder_local_estimate {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} (hF : ¬ F ∅) {r : ℕ} {ε C : ℝ}
    (hε : 0 ≤ ε) (hmin : NearMinimal w r ε (indicator F))
    (hcor : LinkCorrection w r C) {s : Finset V} (hs : Minimal F s) (hr : s.card ≤ r) :
    starNorm w r s (indicator (Path F s)) ≤
      C * starNorm w (r+1) s (delta (indicator (Path F s))) +
        ε * starNorm w r s (indicator F) := by
  let g := indicator (Path F s)
  obtain ⟨b,hb,hbe,hcorr⟩ := hcor s (minimal_nonempty hF hs) hr g
    (fun t ht => indicator_vanish ht)
  have hnear : (1-ε) * starNorm w r s (indicator F) ≤
      starNorm w r s (indicator F + delta b) := by
    rcases lt_or_eq_of_le hr with hlt | heq
    · exact hmin s (minimal_nonempty hF hs) hlt b hb
    · have hd : starNorm w r s (indicator F + delta b) = starNorm w r s (indicator F) := by
        unfold starNorm starSum
        apply Finset.sum_congr rfl
        intro t ht
        simp only [atom,Pi.add_apply,hbe heq t ht,add_zero]
      rw [hd]
      nlinarith [starNorm_nonneg hw r s (indicator F)]
  have hid : indicator F + delta b = (g + delta b) + (indicator F + g) := by
    funext t
    change indicator F t + delta b t = (g t + delta b t) + (indicator F t + g t)
    calc
      _ = (indicator F t + delta b t) + (g t + g t) := by rw [CharTwo.add_self_eq_zero,add_zero]
      _ = _ := by abel
  rw [hid] at hnear
  have hh := starNorm_add_le hw r s (g + delta b) (indicator F + g)
  have hd := ladder_star_difference w F r s
  change starNorm w r s (indicator F + g) = _ at hd
  rw [hd] at hh
  linarith

lemma starNorm_eq_zero_of_card {w : Finset V → ℝ} {r : ℕ} {s : Finset V}
    (hr : r < s.card) (f : Finset V → k) : starNorm w r s f = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  have hn : ¬ s ⊆ t := by intro h; have := Finset.card_le_card h; have := mem_level.mp ht; omega
  exact ite_eq_right hn

lemma boundary_star_estimate {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} {s : Finset V} (hs : Minimal F s) (r : ℕ) :
    starNorm w (r+1) s (delta (indicator (Path F s))) ≤
      starNorm w (r+1) s (delta (indicator F)) +
        starNorm w (r+1) s (indicator (fun T => ¬ NoBad F T)) := by
  unfold starNorm starSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hst : s ⊆ t
  · simp only [ite_eq_left hst]
    by_cases hd : delta (indicator (Path F s)) t = 0
    · simp only [atom,hd]
      split_ifs <;> linarith [hw t]
    · by_cases hn : NoBad F t
      · have hh := localized_boundary_support hs hn hd
        simp only [atom,ite_eq_right hd,ite_eq_right hh]
        exact le_add_of_nonneg_right (by split_ifs <;> linarith [hw t])
      · simp only [atom,ite_eq_right hd,indicator,ite_eq_left hn,one_ne_zero,ite_false]
        exact le_add_of_nonneg_left (by split_ifs <;> linarith [hw t])
  · simp only [ite_eq_right hst,add_zero,le_refl]

theorem fat_ladder_inequality {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} (hF : ¬ F ∅) {r : ℕ} {ε C : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hmin : NearMinimal w r ε (indicator F))
    (hcor : LinkCorrection w r C) :
    (1 - ε*(2:ℝ)^r) * norm w r (indicator F) ≤
       C*(2:ℝ)^(r+1) * (norm w (r+1) (delta (indicator F)) +
         norm w (r+1) (indicator (fun T => ¬ NoBad F T))) := by
  let S := minimalFaces F
  have hloc (s : Finset V) (hs : s ∈ S) :
      starNorm w r s (indicator (Path F s)) ≤
        C * starNorm w (r+1) s (delta (indicator (Path F s))) +
          ε * starNorm w r s (indicator F) := by
    have hsm : Minimal F s := (Finset.mem_filter.mp hs).2
    by_cases hr : s.card ≤ r
    · exact ladder_local_estimate hw hF hε hmin hcor hsm hr
    · rw [starNorm_eq_zero_of_card (lt_of_not_ge hr)]
      exact add_nonneg (mul_nonneg hC (starNorm_nonneg hw _ _ _))
        (mul_nonneg hε (starNorm_nonneg hw _ _ _))
  have hlocsum := Finset.sum_le_sum hloc
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at hlocsum
  have hb : (∑ s ∈ S, starNorm w (r+1) s (delta (indicator (Path F s)))) ≤
      (2:ℝ)^(r+1) * (norm w (r+1) (delta (indicator F)) +
        norm w (r+1) (indicator (fun T => ¬ NoBad F T))) := by
    calc
      _ ≤ (∑ s ∈ S, ( starNorm w (r+1) s (delta (indicator F)) +
          starNorm w (r+1) s (indicator (fun T => ¬ NoBad F T)))) := by
        apply Finset.sum_le_sum
        intro s hs
        exact boundary_star_estimate hw (Finset.mem_filter.mp hs).2 r
      _ = (∑ s ∈ S, starNorm w (r+1) s (delta (indicator F))) +
          (∑ s ∈ S, starNorm w (r+1) s (indicator (fun T => ¬ NoBad F T))) := Finset.sum_add_distrib
      _ ≤ (2:ℝ)^(r+1) * norm w (r+1) (delta (indicator F)) +
          (2:ℝ)^(r+1) * norm w (r+1) (indicator (fun T => ¬ NoBad F T)) :=
        add_le_add (sum_star_le S (r+1) _ (atom_nonneg hw _))
          (sum_star_le S (r+1) _ (atom_nonneg hw _))
      _ = _ := by ring
  have hf : (∑ s ∈ S, starNorm w r s (indicator F)) ≤ (2:ℝ)^r * norm w r (indicator F) :=
    sum_star_le S r _ (atom_nonneg hw _)
  have hcover := norm_le_ladders hw F r
  change norm w r (indicator F) ≤ ∑ s ∈ S, starNorm w r s (indicator (Path F s)) at hcover
  have htotal := hcover.trans (hlocsum.trans
    (add_le_add (mul_le_mul_of_nonneg_left hb hC) (mul_le_mul_of_nonneg_left hf hε)))
  nlinarith

theorem small_set_expansion {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} (hF : ¬ F ∅) {r : ℕ} {ε C : ℝ}
    (hε : 0 ≤ ε) (hC : 0 < C) (hεsmall : ε*(2:ℝ)^r ≤ 1/2)
    (hmin : NearMinimal w r ε (indicator F)) (hcor : LinkCorrection w r C)
    (hbad : C*(2:ℝ)^(r+1) * norm w (r+1) (indicator (fun T => ¬ NoBad F T)) ≤
      (1/4:ℝ) * norm w r (indicator F)) :
    (1/4:ℝ) * norm w r (indicator F) ≤ C*(2:ℝ)^(r+1) *
      norm w (r+1) (delta (indicator F)) := by
  have h := fat_ladder_inequality hw hF hε hC.le hmin hcor
  have hf := norm_nonneg hw r (indicator F)
  have he := mul_le_mul_of_nonneg_right hεsmall hf
  nlinarith

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
lemma chamberWeight_nonneg {A : Type*} [Fintype A] (c : A → Finset V) (μ : A → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (s) : 0 ≤ chamberWeight c μ s := by
  apply Finset.sum_nonneg
  intro a ha
  split_ifs
  · exact hμ a
  · rfl

lemma count_cofaces (s t : Finset V) (R : ℕ) (hsR : s.card ≤ R) :
    ∑ u ∈ level R, (if s ⊆ u ∧ u ⊆ t then (1:ℝ) else 0) =
      if s ⊆ t then (Nat.choose (t.card-s.card) (R-s.card):ℝ) else 0 := by
  by_cases hst : s ⊆ t
  · rw [ite_eq_left hst,← Finset.sum_filter]
    have he : (level R).filter (fun u => s ⊆ u ∧ u ⊆ t) =
        (t.powersetCard R).filter (s ⊆ ·) := by
      ext u
      simp only [Finset.mem_filter,mem_level,Finset.mem_powersetCard]
      tauto
    rw [he]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast Finset.card_filter_powersetCard_subset s t R hst hsR
  · rw [ite_eq_right hst]
    apply Finset.sum_eq_zero
    intro u hu
    exact ite_eq_right (fun hh => hst (hh.1.trans hh.2))

theorem chamberWeight_balance {A : Type*} [Fintype A]
    (c : A → Finset V) (μ : A → ℝ) (N : ℕ) (hc : ∀ a, (c a).card = N)
    (s : Finset V) (R : ℕ) (hsR : s.card ≤ R) :
    starSum R s (chamberWeight c μ) =
      (Nat.choose (N-s.card) (R-s.card):ℝ) * chamberWeight c μ s := by
  unfold starSum chamberWeight
  simp_rw [Finset.mul_sum]
  have he (t : Finset V) :
      (if s ⊆ t then ∑ a, if t ⊆ c a then μ a else 0 else 0) =
        ∑ a, if s ⊆ t ∧ t ⊆ c a then μ a else 0 := by
    by_cases h : s ⊆ t <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have he' : (∑ t ∈ level R, if s ⊆ t ∧ t ⊆ c a then μ a else 0) =
      (∑ t ∈ level R, if s ⊆ t ∧ t ⊆ c a then (1:ℝ) else 0) * μ a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> ring
  rw [he',count_cofaces s (c a) R hsR,hc a]
  split_ifs <;> ring

lemma chamberWeight_balanced {A : Type*} [Fintype A]
    (c : A → Finset V) (μ : A → ℝ) (N : ℕ) (hc : ∀ a, (c a).card = N)
    (hμ : ∀ a, 0 ≤ μ a) : Balanced (chamberWeight c μ) N := by
  refine ⟨chamberWeight_nonneg c μ hμ,?_,chamberWeight_balance c μ N hc⟩
  intro s hs
  apply Finset.sum_eq_zero
  intro a ha
  exact ite_eq_right (by intro h; have := Finset.card_le_card h; rw [hc a] at this; omega)

lemma choose_le_two_pow (n k : ℕ) : (Nat.choose n k : ℝ) ≤ (2:ℝ)^n := by
  exact_mod_cast Nat.choose_le_two_pow n k

lemma Balanced.star_le {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (R : ℕ) : starSum R s w ≤ (2:ℝ)^N * w s := by
  by_cases hs : s.card ≤ R
  · rw [hw.balance s R hs]
    apply mul_le_mul_of_nonneg_right _ (hw.nonneg s)
    exact (choose_le_two_pow _ _).trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
  · have he : starSum R s w = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      exact ite_eq_right (by intro h; have := Finset.card_le_card h; have := mem_level.mp ht; omega)
    rw [he]
    exact mul_nonneg (by positivity) (hw.nonneg s)

lemma Balanced.weight_eq_zero_of_base {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {s t : Finset V} (hst : s ⊆ t) (hs : w s = 0) : w t = 0 := by
  have hle : w t ≤ starSum t.card s w := by
    calc
      w t = (if s ⊆ t then w t else 0) := (ite_eq_left hst).symm
      _ ≤ starSum t.card s w := by
        unfold starSum
        apply Finset.single_le_sum (a := t) (f := fun u : Finset V => if s ⊆ u then w u else 0) _ (mem_level.mpr rfl)
        intro u hu
        split_ifs
        · exact hw.nonneg u
        · rfl
  rw [hw.balance s t.card (Finset.card_le_card hst),hs,mul_zero] at hle
  exact le_antisymm hle (hw.nonneg t)

lemma sum_children (f : Finset V → ℝ) (j : ℕ) :
    (∑ s ∈ level j, starSum (j+1) s f) =
      (j+1:ℝ) * ∑ t ∈ level (j+1), f t := by
  unfold starSum
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have he : (level j).filter (fun s => s ⊆ t) = t.powersetCard j := by
    ext s
    simp only [Finset.mem_filter,mem_level,Finset.mem_powersetCard]
    tauto
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,he,Finset.card_powersetCard]
  have htc := mem_level.mp ht
  rw [htc,Nat.choose_succ_self_right]
  push_cast
  rfl

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
lemma Collision.card {F : Finset V → Prop} {s a : Finset V}
    (h : Collision F s a) : a.card = s.card+2 := by
  obtain ⟨x,hx,y,hy,hxy,he,hfx,hfy⟩ := h
  subst s
  have hye : y ∈ a.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy,hy⟩
  rw [Finset.card_erase_of_mem hye,Finset.card_erase_of_mem hx]
  have hh := Finset.one_le_card.mpr ⟨y,hye⟩
  rw [Finset.card_erase_of_mem hx] at hh
  omega

omit [Fintype V] in
lemma Collision.base_lt {F : Finset V → Prop} {r : ℕ}
    (hcap : ∀ a, F a → a.card ≤ r) {s a : Finset V}
    (h : Collision F s a) : s.card < r := by
  have hc := h.card
  obtain ⟨x,hx,y,hy,hxy,he,hfx,hfy⟩ := h
  have hf := hcap _ hfx
  rw [Finset.card_erase_of_mem hx] at hf
  omega

lemma bad_face_cover {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} {r : ℕ} (hcap : ∀ a, F a → a.card ≤ r) (T : Finset V) :
    atom w (indicator (fun T => ¬ NoBad F T)) T ≤
      ∑ s ∈ thinBases F r, ∑ a ∈ level (s.card+2),
        if Collision F s a ∧ a ⊆ T then w T else 0 := by
  have hn (s : Finset V) : 0 ≤ ∑ a ∈ level (s.card+2),
        if Collision F s a ∧ a ⊆ T then w T else 0 := by
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact hw T
    · rfl
  by_cases hbad : ¬ NoBad F T
  · have h := hbad
    unfold NoBad at h
    push Not at h
    obtain ⟨a,ha,x,hx,y,hy,hxy,hfx,hfy,hthin⟩ := h
    let s := (a.erase x).erase y
    have hcol : Collision F s a := ⟨x,hx,y,hy,hxy,rfl,hfx,hfy⟩
    have hs : s ∈ thinBases F r := by
      simp only [thinBases,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hcol.base_lt hcap,hthin⟩
    have hle : w T ≤ ∑ b ∈ level (s.card+2),
        if Collision F s b ∧ b ⊆ T then w T else 0 := by
      calc
        w T = (if Collision F s a ∧ a ⊆ T then w T else 0) := (ite_eq_left ⟨hcol,ha⟩).symm
        _ ≤ _ := by
          apply Finset.single_le_sum (a := a) _ (mem_level.mpr hcol.card)
          intro b hb
          split_ifs
          · exact hw T
          · rfl
    simp only [atom,indicator,ite_eq_left hbad,one_ne_zero,ite_false]
    exact hle.trans (Finset.single_le_sum (fun s _ => hn s) hs)
  · simp only [atom,indicator,ite_eq_right hbad,ite_true]
    exact Finset.sum_nonneg (fun s _ => hn s)

theorem bad_mass_le {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    {F : Finset V → Prop} (hcap : ∀ a, F a → a.card ≤ r) (R : ℕ) :
    norm w R (indicator (fun T => ¬ NoBad F T)) ≤
      (2:ℝ)^N * ∑ s ∈ thinBases F r, collisionMass w F s := by
  calc
    _ ≤ ∑ T ∈ level R, ∑ s ∈ thinBases F r, ∑ a ∈ level (s.card+2),
        if Collision F s a ∧ a ⊆ T then w T else 0 :=
      Finset.sum_le_sum (fun T hT => bad_face_cover hw.nonneg hcap T)
    _ = ∑ s ∈ thinBases F r, ∑ a ∈ level (s.card+2),
        if Collision F s a then starSum R a w else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hcol : Collision F s a <;> simp [hcol,starSum]
    _ ≤ (2:ℝ)^N * ∑ s ∈ thinBases F r, collisionMass w F s := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      unfold collisionMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      by_cases hcol : Collision F s a
      · simp only [ite_eq_left hcol]
        exact hw.star_le a R
      · simp only [ite_eq_right hcol,mul_zero,le_refl]

omit [DecidableEq V] in
lemma level_eq_filter (j : ℕ) : level (V:=V) j = Finset.univ.filter (fun s => s.card = j) := by
  ext s
  simp

omit [DecidableEq V] in
lemma sum_thinBases (F : Finset V → Prop) (r : ℕ) (f : Finset V → ℝ) :
    (∑ s ∈ thinBases F r, f s) =
      ∑ j ∈ Finset.range r, ∑ s ∈ level j, if F s then 0 else f s := by
  unfold thinBases
  rw [Finset.sum_filter]
  simp_rw [level_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hf : F s
  · simp [hf]
  · simp [hf]

theorem degeneracy_estimate {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hrN : r ≤ N) {F : Finset V → Prop} (hcap : ∀ a, F a → a.card ≤ r)
    (θ : ℕ → ℝ) (lam : ℝ) (hθ : ∀ j < r, 0 ≤ θ j+lam)
    (hpair : ∀ s, s.card < r → ¬ F s →
      collisionMass w F s ≤ (θ s.card+lam)*(N:ℝ)*
        starNorm w (s.card+1) s (indicator F)) (R : ℕ) :
    norm w R (indicator (fun T => ¬NoBad F T)) ≤
      (2:ℝ)^N * (N:ℝ)^2 *
        ∑ j ∈ Finset.range r, (θ j+lam)*norm w (j+1) (indicator F) := by
  apply (bad_mass_le hw hcap R).trans
  rw [sum_thinBases]
  have hsum : (∑ j ∈ Finset.range r, ∑ s ∈ level j,
      if F s then 0 else collisionMass w F s) ≤
      (N:ℝ)^2 * ∑ j ∈ Finset.range r, (θ j+lam)*norm w (j+1) (indicator F) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_range.mp hj
    have hc : 0 ≤ (θ j+lam)*(N:ℝ) := mul_nonneg (hθ j hjr) (Nat.cast_nonneg N)
    calc
      _ ≤ ∑ s ∈ level j, (θ j+lam)*(N:ℝ)*starNorm w (j+1) s (indicator F) := by
        apply Finset.sum_le_sum
        intro s hs
        have he := mem_level.mp hs
        by_cases hf : F s
        · rw [ite_eq_left hf]
          exact mul_nonneg hc (starNorm_nonneg hw.nonneg _ _ _)
        · rw [ite_eq_right hf]
          simpa only [he] using hpair s (by omega) hf
      _ = (θ j+lam)*(N:ℝ)*(j+1:ℝ)*norm w (j+1) (indicator F) := by
        rw [← Finset.mul_sum]
        change (θ j+lam)*(N:ℝ)*(∑ s ∈ level j, starSum (j+1) s (atom w (indicator F))) = _
        rw [sum_children]
        simp only [norm,mul_assoc]
      _ ≤ (N:ℝ)^2*((θ j+lam)*norm w (j+1) (indicator F)) := by
        have hjN : (j+1:ℝ) ≤ N := by exact_mod_cast (show j+1 ≤ N by omega)
        have hn := norm_nonneg hw.nonneg (j+1) (indicator F)
        nlinarith [mul_le_mul_of_nonneg_left hjN (mul_nonneg hc hn)]
  have h := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 2^N by positivity)
  simpa only [mul_assoc] using h

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma fatFamily_cap (w : Finset V → ℝ) (N r : ℕ) (θ : ℕ → ℝ) (f : Finset V → k) :
    ∀ s, fatFamily w N r θ f s → s.card ≤ r := fun _ h => h.1

lemma fatFamily_recurrence (w : Finset V → ℝ) (N r : ℕ) (θ : ℕ → ℝ)
    (f : Finset V → k) (s : Finset V) (hs : s.card < r) :
    fatFamily w N r θ f s ↔ 0 < w s ∧
      θ s.card * (N-s.card:ℕ) * w s ≤
        starNorm w (s.card+1) s (indicator (fatFamily w N r θ f)) := by
  have he : r-s.card = (r-s.card-1)+1 := by omega
  have hh : starNorm w (s.card+1) s (indicator (fatAt w N θ f (r-s.card-1))) =
      starNorm w (s.card+1) s (indicator (fatFamily w N r θ f)) := by
    unfold starNorm starSum
    apply Finset.sum_congr rfl
    intro t ht
    have htc := mem_level.mp ht
    have htr : t.card ≤ r := by omega
    have hidx : r-t.card = r-s.card-1 := by omega
    simp only [atom_indicator,fatFamily,htr,true_and,hidx]
  unfold fatFamily
  rw [he]
  simp only [fatAt,show s.card ≤ r from hs.le,true_and]
  rw [hh]
  rfl

lemma fatFamily_top_norm {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (N r : ℕ) (θ : ℕ → ℝ) (f : Finset V → k) :
    norm w r (indicator (fatFamily w N r θ f)) = norm w r f := by
  apply Finset.sum_congr rfl
  intro s hs
  have hc := mem_level.mp hs
  simp only [atom_indicator,fatFamily,hc,Nat.sub_self,le_refl,true_and,fatAt]
  by_cases hf : f s = 0
  · simp [hf,atom]
  · by_cases hp : 0 < w s
    · simp [hf,hp,atom]
    · have hz : w s = 0 := le_antisymm (le_of_not_gt hp) (hw s)
      simp [hz,atom]

theorem fat_markov {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hrN : r ≤ N) (θ : ℕ → ℝ) (hθ : ∀ j < r, 0 ≤ θ j)
    (f : Finset V → k) (j : ℕ) (hj : j < r) :
    θ j * norm w j (indicator (fatFamily w N r θ f)) ≤
      (N:ℝ) * norm w (j+1) (indicator (fatFamily w N r θ f)) := by
  let F := fatFamily w N r θ f
  have hlocal (s : Finset V) (hs : s ∈ level j) :
      θ j * (N-j:ℕ) * atom w (indicator F) s ≤
        starNorm w (j+1) s (indicator F) := by
    have he := mem_level.mp hs
    by_cases hf : F s
    · have h := (fatFamily_recurrence w N r θ f s (by omega)).mp hf
      simpa only [atom_indicator,ite_eq_left hf,he] using h.2
    · simp only [atom_indicator,ite_eq_right hf,mul_zero]
      exact starNorm_nonneg hw.nonneg _ _ _
  have hsum := Finset.sum_le_sum hlocal
  simp only [← Finset.mul_sum] at hsum
  change θ j * (N-j:ℕ) * norm w j (indicator F) ≤
    ∑ s ∈ level j, starSum (j+1) s (atom w (indicator F)) at hsum
  rw [sum_children] at hsum
  change θ j * (N-j:ℕ) * norm w j (indicator F) ≤
    (j+1:ℝ)*norm w (j+1) (indicator F) at hsum
  have hn := norm_nonneg hw.nonneg j (indicator F)
  have hn' := norm_nonneg hw.nonneg (j+1) (indicator F)
  have hnj : (1:ℝ) ≤ (N-j:ℕ) := by exact_mod_cast (show 1 ≤ N-j by omega)
  have hjN : (j+1:ℝ) ≤ N := by exact_mod_cast (show j+1 ≤ N by omega)
  have hleft := mul_le_mul_of_nonneg_right hnj (mul_nonneg (hθ j hj) hn)
  have hright := mul_le_mul_of_nonneg_right hjN hn'
  change θ j * norm w j (indicator F) ≤ _
  nlinarith

lemma fatBudget_pos {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    0 < fatBudget N η k := by
  induction k with
  | zero => norm_num [fatBudget]
  | succ k ih => simp only [fatBudget]; positivity

lemma fatThreshold_pos {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) (r j : ℕ) :
    0 < fatThreshold N r η j := div_pos hη (fatBudget_pos hN hη _)

theorem fat_mass_bound {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) {η : ℝ} (hη : 0 < η) (f : Finset V → k)
    (a : ℕ) (ha : a ≤ r) :
    norm w (r-a) (indicator (fatFamily w N r (fatThreshold N r η) f)) ≤
      fatBudget N η a * norm w r f := by
  let θ := fatThreshold N r η
  let F := fatFamily w N r θ f
  induction a with
  | zero =>
      simp only [Nat.sub_zero,fatBudget,one_mul]
      exact le_of_eq (fatFamily_top_norm hw.nonneg N r θ f)
  | succ a ih =>
      have har : a ≤ r := by omega
      have hi := ih har
      have hj : r-(a+1) < r := by omega
      have ht : θ (r-(a+1)) = η / fatBudget N η a := by
        unfold θ fatThreshold
        congr 2
        omega
      have hidx : r-(a+1)+1 = r-a := by omega
      have hm := fat_markov hw hrN θ (fun j _ => (fatThreshold_pos hN hη r j).le) f _ hj
      change θ (r-(a+1))*norm w (r-(a+1)) (indicator F) ≤
        (N:ℝ)*norm w (r-(a+1)+1) (indicator F) at hm
      rw [ht,hidx] at hm
      have hb := fatBudget_pos hN hη a
      have hh := hm.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg N))
      have hdiv : 0 < η / fatBudget N η a := div_pos hη hb
      have hh' : norm w (r-(a+1)) (indicator F) ≤
          (N:ℝ)*(fatBudget N η a*norm w r f)/(η/fatBudget N η a) :=
        (le_div_iff₀ hdiv).mpr (by simpa only [mul_comm] using hh)
      calc
        _ ≤ (N:ℝ) * (fatBudget N η a * norm w r f) / (η / fatBudget N η a) := hh'
        _ = fatBudget N η (a+1)*norm w r f := by
          simp only [fatBudget]
          field_simp

lemma fat_empty_false {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) (hw0 : w ∅ = 1) {η : ℝ} (hη : 0 < η)
    (f : Finset V → k) (hf : norm w r f < 1 / fatBudget N η r) :
    ¬ fatFamily w N r (fatThreshold N r η) f ∅ := by
  intro hF
  have hm := fat_mass_bound hw hN hrN hη f r le_rfl
  have he : norm w 0 (indicator (fatFamily w N r (fatThreshold N r η) f)) = 1 := by
    simp [norm,level,atom_indicator,hF,hw0]
  rw [Nat.sub_self,he] at hm
  have hb := fatBudget_pos hN hη r
  have hlt := (lt_div_iff₀ hb).mp hf
  nlinarith

end

variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] in
lemma atom_le_weight {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (f : Finset V → k) (s) :
    atom w f s ≤ w s := by unfold atom; split_ifs; exact hw s; rfl

lemma starNorm_le_starSum {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r s) (f : Finset V → k) :
    starNorm w r s f ≤ starSum r s w := starSum_mono (fun _ _ _ => atom_le_weight hw f _)

lemma fat_thin_children {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (θ : ℕ → ℝ) (f : Finset V → k) (s : Finset V) (hs : s.card < r)
    (hf : ¬ fatFamily w N r θ f s) :
    starNorm w (s.card+1) s (indicator (fatFamily w N r θ f)) ≤
      θ s.card * (N-s.card:ℕ) * w s := by
  by_cases hp : 0 < w s
  · have hn : ¬ θ s.card * (N-s.card:ℕ) * w s ≤
        starNorm w (s.card+1) s (indicator (fatFamily w N r θ f)) := by
      intro h
      exact hf ((fatFamily_recurrence w N r θ f s hs).mpr ⟨hp,h⟩)
    exact (lt_of_not_ge hn).le
  · have hz : w s = 0 := le_antisymm (le_of_not_gt hp) (hw.nonneg s)
    have hh := starNorm_le_starSum hw.nonneg (s.card+1) s
      (indicator (fatFamily w N r θ f))
    rw [hw.balance s (s.card+1) (by omega),hz,mul_zero] at hh
    simpa only [hz,mul_zero] using hh

theorem fat_degeneracy_bound {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) {η lam : ℝ} (hη : 0 < η) (hlam : 0 ≤ lam)
    (hbudget : ∀ a ≤ r, lam * fatBudget N η a ≤ η)
    (hmix : LocalMixing w N lam) (f : Finset V → k) (R : ℕ) :
    norm w R (indicator (fun T => ¬NoBad (fatFamily w N r (fatThreshold N r η) f) T)) ≤
      (2:ℝ)^N * (N:ℝ)^2 * (r:ℝ) * (2*η) * norm w r f := by
  let θ := fatThreshold N r η
  let F := fatFamily w N r θ f
  have hpair : ∀ s, s.card < r → ¬F s → collisionMass w F s ≤
      (θ s.card+lam)*(N:ℝ)*starNorm w (s.card+1) s (indicator F) := by
    intro s hs hf
    exact hmix F s (by omega) (θ s.card) (fatThreshold_pos hN hη r s.card).le
      (fat_thin_children hw θ f s hs hf)
  have hd := degeneracy_estimate hw hrN (fatFamily_cap w N r θ f) θ lam
    (fun j _ => add_nonneg (fatThreshold_pos hN hη r j).le hlam) hpair R
  have hs : (∑ j ∈ Finset.range r, (θ j+lam)*norm w (j+1) (indicator F)) ≤
      (r:ℝ)*(2*η)*norm w r f := by
    calc
      _ ≤ ∑ j ∈ Finset.range r, (2*η)*norm w r f := by
        apply Finset.sum_le_sum
        intro j hj
        have hjr := Finset.mem_range.mp hj
        have hidx : r-(r-j-1) = j+1 := by omega
        have hb := fatBudget_pos hN hη (r-j-1)
        have hm := fat_mass_bound hw hN hrN hη f (r-j-1) (by omega)
        rw [hidx] at hm
        have hθlam : 0 ≤ θ j+lam := add_nonneg (fatThreshold_pos hN hη r j).le hlam
        calc
          (θ j+lam)*norm w (j+1) (indicator F) ≤
              (θ j+lam)*(fatBudget N η (r-j-1)*norm w r f) :=
            mul_le_mul_of_nonneg_left hm hθlam
          _ = (η+lam*fatBudget N η (r-j-1))*norm w r f := by
            unfold θ fatThreshold
            field_simp
          _ ≤ (2*η)*norm w r f := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg hw.nonneg r f)
            linarith [hbudget (r-j-1) (by omega)]
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
  have hmult := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 2^N*(N:ℝ)^2 by positivity)
  exact hd.trans (by simpa only [mul_assoc] using hmult)

theorem exists_mixing_tolerance (N r : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ a ≤ r, lam*fatBudget N η a ≤ η := by
  let S := ∑ a ∈ Finset.range (r+1), fatBudget N η a
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a _ => (fatBudget_pos hN hη a).le)
  have hden : 0 < 1+S := by linarith
  refine ⟨η/(1+S),div_pos hη hden,?_⟩
  intro a ha
  have hle : fatBudget N η a ≤ S := Finset.single_le_sum
    (fun b _ => (fatBudget_pos hN hη b).le) (Finset.mem_range.mpr (by omega))
  have hh : fatBudget N η a ≤ 1+S := by linarith
  calc
    η/(1+S)*fatBudget N η a ≤ η/(1+S)*(1+S) :=
      mul_le_mul_of_nonneg_left hh (div_pos hη hden).le
    _ = η := div_mul_cancel₀ η (ne_of_gt hden)

end CoboundaryExpanders.FatLadders

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Self-adjoint operator estimates and the weighted-graph spectral trickling argument.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Spectral

section

lemma eigenvalue_trickle {lam μ : ℝ} (hlam : lam < 1) (hμ : μ < 1)
    (h : μ ≤ lam + (1-lam)*μ^2) : μ ≤ lam/(1-lam) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-lam)).mpr
  have hp : 0 < 1-μ := by linarith
  nlinarith [mul_pos hp (by linarith : 0 < 1-lam)]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem operator_trickle (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (c : E) (hfix : ∀ v, A v = v → ∃ t : ℝ, v = t • c)
    {lam : ℝ} (hlam : lam < 1)
    (hupper : ∀ v, ⟪A v,v⟫_ℝ ≤ ⟪v,v⟫_ℝ)
    (hlocal : ∀ v, ⟪A v,v⟫_ℝ ≤ lam*⟪v,v⟫_ℝ + (1-lam)*⟪A v,A v⟫_ℝ)
    (v : E) (hv : ⟪c,v⟫_ℝ = 0) :
    ⟪A v,v⟫_ℝ ≤ lam/(1-lam) * ⟪v,v⟫_ℝ := by
  classical
  let b := hA.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let ev := hA.eigenvalues (n := Module.finrank ℝ E) rfl
  have he (i) : A (b i) = ev i • b i := hA.apply_eigenvectorBasis rfl i
  have hn (i) : ⟪b i,b i⟫_ℝ = 1 := by
    simp
  have hi (i) : ev i ≤ 1 := by
    have h := hupper (b i)
    rw [he,real_inner_smul_left,hn,mul_one] at h
    exact h
  have hbound (i) : ev i * (b.repr v i)^2 ≤ lam/(1-lam) * (b.repr v i)^2 := by
    by_cases h : ev i = 1
    · have hh : A (b i) = b i := by rw [he,h,one_smul]
      obtain ⟨t,ht⟩ := hfix (b i) hh
      have hvi : b.repr v i = 0 := by
        rw [OrthonormalBasis.repr_apply_apply,ht,real_inner_smul_left,hv,mul_zero]
      simp [hvi]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply eigenvalue_trickle hlam (lt_of_le_of_ne (hi i) h)
      have hl := hlocal (b i)
      rw [he,real_inner_smul_left,real_inner_smul_right,real_inner_smul_left,hn] at hl
      nlinarith
  have hrepr : ∀ i, b.repr (A v) i = ev i * b.repr v i :=
    hA.eigenvectorBasis_apply_self_apply rfl v
  rw [← b.repr.inner_map_map (A v) v, ← b.repr.inner_map_map v v]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hrepr]
  nlinarith [hbound i]

end

open scoped BigOperators InnerProductSpace
variable {V : Type} [Fintype V]

namespace WeightedGraph
open WithLp
variable (G : WeightedGraph V)

lemma mass_pos (u : V) : 0 < G.mass u := G.row_pos u
lemma mass_ne (u : V) : G.mass u ≠ 0 := ne_of_gt (G.mass_pos u)

lemma swapped_energy (f : V → ℝ) :
    (∑ u, ∑ v, G.edge u v * (f v)^2) = G.energy f := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [mass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [G.symm]

lemma energy_difference (f : V → ℝ) :
    G.energy f - G.pairing f f = (1/2:ℝ) * ∑ u, ∑ v, G.edge u v * (f u-f v)^2 := by
  have hswap := G.swapped_energy f
  have hself : (∑ u, ∑ v, G.edge u v * (f u)^2) = G.energy f := by
    simp only [energy,mass,Finset.sum_mul]
  have he : (∑ u, ∑ v, G.edge u v * (f u-f v)^2) =
      (∑ u, ∑ v, G.edge u v * (f u)^2) + (∑ u, ∑ v, G.edge u v * (f v)^2) -
        2 * G.pairing f f := by
    simp only [pairing,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he,hself,hswap]
  ring

lemma pairing_le_energy (f : V → ℝ) : G.pairing f f ≤ G.energy f := by
  have hn : 0 ≤ ∑ u, ∑ v, G.edge u v * (f u-f v)^2 :=
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
      mul_nonneg (G.nonneg u v) (sq_nonneg _)))
  have hh := G.energy_difference f
  linarith

lemma action_pairing (f g : V → ℝ) :
    (∑ u, G.mass u * f u * G.action g u) = G.pairing f g := by
  unfold pairing action
  apply Finset.sum_congr rfl
  intro u _
  calc
    G.mass u * f u * ((∑ v, G.edge u v * g v)/G.mass u) =
        f u * (∑ v, G.edge u v * g v) := by field_simp [G.mass_ne u]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring

lemma fixed_constant (hG : G.Connected) (f : V → ℝ) (hf : G.action f = f) :
    ∀ u v, f u = f v := by
  have he : G.energy f = G.pairing f f := by
    rw [← G.action_pairing, hf]
    simp only [energy,pow_two,mul_assoc]
  have hz : ∑ u, ∑ v, G.edge u v * (f u-f v)^2 = 0 := by
    have h := G.energy_difference f
    rw [he,sub_self] at h
    linarith
  have hn (u v) : 0 ≤ G.edge u v * (f u-f v)^2 :=
    mul_nonneg (G.nonneg u v) (sq_nonneg _)
  have hedge (u v) (huv : 0 < G.edge u v) : f u = f v := by
    have hrow : ∑ v, G.edge u v * (f u-f v)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => hn u v))).mp hz
        u (Finset.mem_univ u)
    have hs : G.edge u v * (f u-f v)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hn u v)).mp hrow v (Finset.mem_univ v)
    have hsq := (mul_eq_zero.mp hs).resolve_left (ne_of_gt huv)
    nlinarith [sq_nonneg (f u-f v)]
  intro u v
  induction hG u v with
  | refl => rfl
  | @tail b c _ hbc ih => exact ih.trans (hedge b c hbc)

lemma sqrt_ne (u : V) : Real.sqrt (G.mass u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (G.mass_pos u))
@[simp] lemma coord_uncoord (v : EuclideanSpace ℝ V) : G.coord (G.uncoord v) = v := by
  ext u
  simp only [coord,uncoord,PiLp.toLp_apply,mul_div_cancel₀ _ (G.sqrt_ne u)]
@[simp] lemma uncoord_coord (f : V → ℝ) : G.uncoord (G.coord f) = f := by
  funext u
  simp only [coord,uncoord,PiLp.toLp_apply,mul_div_cancel_left₀ _ (G.sqrt_ne u)]

lemma coord_inner (f g : V → ℝ) :
    ⟪G.coord f,G.coord g⟫_ℝ = ∑ u, G.mass u * f u * g u := by
  simp only [coord,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro u _
  calc
    _ = (Real.sqrt (G.mass u))^2 * f u * g u := by ring
    _ = _ := by rw [Real.sq_sqrt (G.mass_pos u).le]

lemma operator_coord (f : V → ℝ) : G.operator (G.coord f) = G.coord (G.action f) := by
  ext u
  change (∑ v, G.edge u v / (Real.sqrt (G.mass u)*Real.sqrt (G.mass v)) *
    (Real.sqrt (G.mass v)*f v)) = Real.sqrt (G.mass u)*((∑ v,G.edge u v*f v)/G.mass u)
  rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hs := Real.sq_sqrt (G.mass_pos u).le
  field_simp [G.sqrt_ne u,G.sqrt_ne v,G.mass_ne u]
  rw [hs]
  ring

attribute [local instance] OAI.CoboundaryExpanders.Spectral.WeightedGraph.instDecidableEq
lemma operator_symmetric : G.operator.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext u v
  simp only [Matrix.conjTranspose_apply,star_trivial,matrix]
  rw [G.symm v u,mul_comm]

theorem trickle [Nonempty V] (hG : G.Connected) {lam : ℝ} (hlam : lam < 1)
    (hloc : ∀ f : V → ℝ, G.pairing f f ≤ lam*G.energy f + (1-lam)*G.energy (G.action f))
    (f : V → ℝ) (hf : ∑ u, G.mass u * f u = 0) :
    G.pairing f f ≤ (lam/(1-lam))*G.energy f := by
  let c := G.coord (fun _ => 1)
  have hfix (v : EuclideanSpace ℝ V) (hv : G.operator v = v) : ∃ t : ℝ, v = t • c := by
    have hh : G.action (G.uncoord v) = G.uncoord v := by
      have h := congrArg G.uncoord hv
      rw [← G.coord_uncoord v,G.operator_coord,G.uncoord_coord] at h
      simpa using h
    let u : V := Classical.choice inferInstance
    refine ⟨G.uncoord v u,?_⟩
    conv_lhs => rw [← G.coord_uncoord v]
    ext w
    change Real.sqrt (G.mass w)*G.uncoord v w = G.uncoord v u * (Real.sqrt (G.mass w)*1)
    rw [G.fixed_constant hG _ hh w u]
    ring
  have hup (v : EuclideanSpace ℝ V) : ⟪G.operator v,v⟫_ℝ ≤ ⟪v,v⟫_ℝ := by
    rw [← G.coord_uncoord v,G.operator_coord,G.coord_inner,G.coord_inner]
    have h := G.pairing_le_energy (G.uncoord v)
    rw [← G.action_pairing] at h
    simpa only [energy,pow_two,mul_assoc,mul_left_comm,mul_comm] using h
  have hlo (v : EuclideanSpace ℝ V) : ⟪G.operator v,v⟫_ℝ ≤
      lam*⟪v,v⟫_ℝ + (1-lam)*⟪G.operator v,G.operator v⟫_ℝ := by
    rw [← G.coord_uncoord v,G.operator_coord,G.coord_inner,G.coord_inner,G.coord_inner]
    have h := hloc (G.uncoord v)
    rw [← G.action_pairing] at h
    simpa only [energy,pow_two,mul_assoc,mul_left_comm,mul_comm] using h
  have hmean : ⟪c,G.coord f⟫_ℝ = 0 := by simpa [c,G.coord_inner] using hf
  have h := operator_trickle G.operator G.operator_symmetric c hfix hlam hup hlo (G.coord f) hmean
  rw [G.operator_coord,G.coord_inner,G.coord_inner] at h
  rw [← G.action_pairing]
  simpa only [energy,pow_two,mul_assoc,mul_left_comm,mul_comm] using h

end WeightedGraph
end CoboundaryExpanders.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Mixing
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Small-set expansion, local spectral descent, connectedness, and uniform coset mixing.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.EdgeMixing
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

lemma mean_chi (e : V → V → ℝ) (P : V → Prop) :
    (∑ x, mass e x * chi P x) = selected e P := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : P x <;> simp [chi,h]

lemma sum_right (e : V → V → ℝ) (hs : ∀ x y, e x y = e y x) (f : V → ℝ) :
    (∑ x, ∑ y, e x y * f y) = ∑ x, mass e x * f x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [hs]

lemma centered_mean (e : V → V → ℝ) (P : V → Prop) :
    (∑ x, mass e x * (volume e * chi P x - selected e P)) = 0 := by
  simp only [mul_sub,Finset.sum_sub_distrib]
  have h : (∑ x, mass e x * (volume e * chi P x)) = volume e * selected e P := by
    rw [← mean_chi,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h,← Finset.sum_mul]
  change volume e * selected e P - volume e * selected e P = 0
  ring

lemma centered_energy (e : V → V → ℝ) (P : V → Prop) :
    energy e (fun x => volume e * chi P x - selected e P) =
      (volume e)^2*selected e P-volume e*(selected e P)^2 := by
  have he : energy e (fun x => volume e * chi P x - selected e P) =
      (volume e)^2*(∑ x, mass e x * chi P x) -
      2*volume e*selected e P*(∑ x, mass e x * chi P x) +
      (selected e P)^2*(∑ x, mass e x) := by
    simp only [energy,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : P x <;> simp [chi, h] <;> ring
  rw [he,mean_chi]
  change (volume e)^2*selected e P - 2*volume e*selected e P*selected e P +
    (selected e P)^2*volume e = _
  ring

lemma centered_pairing (e : V → V → ℝ) (hs : ∀ x y, e x y = e y x) (P : V → Prop) :
    pairing e (fun x => volume e * chi P x - selected e P)
      (fun x => volume e * chi P x - selected e P) =
    (volume e)^2*pairing e (chi P) (chi P)-volume e*(selected e P)^2 := by
  have he : pairing e (fun x => volume e * chi P x - selected e P)
      (fun x => volume e * chi P x - selected e P) =
      (volume e)^2*pairing e (chi P) (chi P) -
      volume e*selected e P*(∑ x, ∑ y, e x y * chi P x) -
      volume e*selected e P*(∑ x, ∑ y, e x y * chi P y) +
      (selected e P)^2*volume e := by
    simp only [pairing,volume,mass,Finset.mul_sum,← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hl : (∑ x, ∑ y, e x y * chi P x) = selected e P := by
    simp only [← Finset.sum_mul]
    exact mean_chi e P
  rw [he,hl,sum_right e hs,mean_chi]
  ring

theorem small_set (e : V → V → ℝ) (he : ∀ x y, 0 ≤ e x y)
    (hs : ∀ x y, e x y = e y x) (hvol : 0 < volume e)
    {lam t : ℝ} (hlam : 0 ≤ lam) (hray : Rayleigh e lam)
    (P : V → Prop) (hP : selected e P ≤ t*volume e) :
    pairing e (chi P) (chi P) ≤ (t+lam)*selected e P := by
  have ha : 0 ≤ selected e P := Finset.sum_nonneg (fun x _ => by
    split_ifs
    · exact Finset.sum_nonneg (fun y _ => he x y)
    · rfl)
  have hh := hray (fun x => volume e * chi P x - selected e P) (centered_mean e P)
  rw [centered_pairing e hs,centered_energy] at hh
  have hb : volume e*(selected e P)^2 ≤ t*(volume e)^2*selected e P := by
    nlinarith [mul_le_mul_of_nonneg_right hP (mul_nonneg hvol.le ha)]
  have hn : 0 ≤ lam*volume e*(selected e P)^2 := by positivity
  have hv : 0 < (volume e)^2 := sq_pos_of_pos hvol
  nlinarith

end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
lemma coface_eq_insert {s a : Finset V} (hsub : s ⊆ a) (hc : a.card = s.card+1) :
    ∃ x, x ∉ s ∧ insert x s = a := by
  obtain ⟨x,hxa,hxs⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : s.card < a.card)
  refine ⟨x,hxs,Finset.eq_of_subset_of_card_le (Finset.insert_subset hxa hsub) ?_⟩
  rw [Finset.card_insert_of_notMem hxs,hc]

lemma sum_insert_star (s : Finset V) (g : Finset V → ℝ) :
    (∑ x : V, if x ∉ s then g (insert x s) else 0) = starSum (s.card+1) s g := by
  unfold starSum
  rw [← Finset.sum_filter,← Finset.sum_filter]
  apply Finset.sum_bij (fun x _ => insert x s)
  · intro x hx
    have hn := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨mem_level.mpr (Finset.card_insert_of_notMem hn),
      Finset.subset_insert _ _⟩
  · intro x hx y hy he
    have hxs := (Finset.mem_filter.mp hx).2
    have hys := (Finset.mem_filter.mp hy).2
    have hm : x ∈ insert y s := he ▸ Finset.mem_insert_self x s
    exact (Finset.mem_insert.mp hm).resolve_right hxs
  · intro a ha
    obtain ⟨ha,hsub⟩ := Finset.mem_filter.mp ha
    obtain ⟨x,hx,he⟩ := coface_eq_insert hsub (mem_level.mp ha)
    exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,he⟩
  · intro x hx
    rfl

omit [Fintype V] in
lemma linkEdge_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (s x y) :
    0 ≤ linkEdge w s x y := by unfold linkEdge; split_ifs; exact hw _; rfl
omit [Fintype V] in
lemma linkEdge_symm (w : Finset V → ℝ) (s : Finset V) (x y : V) :
    linkEdge w s x y = linkEdge w s y x := by
  simp only [linkEdge,Finset.insert_comm,ne_comm,and_comm,and_left_comm,and_assoc]

lemma linkEdge_mass {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (x : V) :
    EdgeMixing.mass (linkEdge w s) x =
      if x ∉ s then (N-s.card-1:ℕ)*w (insert x s) else 0 := by
  by_cases hx : x ∈ s
  · simp [EdgeMixing.mass,linkEdge,hx]
  · rw [ite_eq_left hx]
    have he : EdgeMixing.mass (linkEdge w s) x =
        ∑ y : V, if y ∉ insert x s then w (insert y (insert x s)) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ s
      · simp [linkEdge,hy]
      · by_cases hxy : x = y
        · subst y; simp [linkEdge]
        · simp [linkEdge,hx,hy,hxy,Ne.symm hxy,Finset.insert_comm]
    rw [he,sum_insert_star,hw.balance _ _ (by omega)]
    simp [Finset.card_insert_of_notMem hx,Nat.sub_add_eq]

lemma linkEdge_selected {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (F : Finset V → Prop) (s : Finset V) :
    EdgeMixing.selected (linkEdge w s) (fun x => F (insert x s)) =
      (N-s.card-1:ℕ)*starNorm w (s.card+1) s (indicator F) := by
  have he : EdgeMixing.selected (linkEdge w s) (fun x => F (insert x s)) =
      (N-s.card-1:ℕ)*(∑ x : V, if x ∉ s then atom w (indicator F) (insert x s) else 0) := by
    simp only [EdgeMixing.selected,linkEdge_mass hw,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [atom_indicator]
    split_ifs <;> ring
  rw [he,sum_insert_star]
  rfl

lemma linkEdge_volume {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) :
    EdgeMixing.volume (linkEdge w s) =
      (N-s.card-1:ℕ)*(N-s.card:ℕ)*w s := by
  have he : EdgeMixing.volume (linkEdge w s) =
      (N-s.card-1:ℕ)*(∑ x : V, if x ∉ s then w (insert x s) else 0) := by
    simp only [EdgeMixing.volume,linkEdge_mass hw,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [he,sum_insert_star,hw.balance _ _ (by omega)]
  simp [mul_assoc]

omit [Fintype V] in
lemma Collision.reconstruct {F : Finset V → Prop} {s a : Finset V}
    (hc : Collision F s a) : ∃ x y, x ∉ s ∧ y ∉ s ∧ x ≠ y ∧
      a = insert x (insert y s) ∧ F (insert x s) ∧ F (insert y s) := by
  obtain ⟨x,hx,y,hy,hxy,he,hfx,hfy⟩ := hc
  have hye : y ∈ a.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy,hy⟩
  have hey : insert y s = a.erase x := by rw [←he,Finset.insert_erase hye]
  have hrep : insert x (insert y s) = a := by rw [hey,Finset.insert_erase hx]
  have hex : insert x s = a.erase y := by
    rw [←he,Finset.erase_right_comm,Finset.insert_erase]
    exact Finset.mem_erase.mpr ⟨hxy,hx⟩
  refine ⟨x,y,?_,?_,hxy,hrep.symm,hex ▸ hfy,hey ▸ hfx⟩
  · rw [←he]; simp
  · rw [←he]; simp

lemma collision_le_pairing {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (F : Finset V → Prop) (s : Finset V) :
    collisionMass w F s ≤ EdgeMixing.pairing (linkEdge w s)
      (EdgeMixing.chi (fun x => F (insert x s))) (EdgeMixing.chi (fun x => F (insert x s))) := by
  let term := fun x y => linkEdge w s x y * EdgeMixing.chi (fun x => F (insert x s)) x *
    EdgeMixing.chi (fun x => F (insert x s)) y
  have ht : ∀ x y, 0 ≤ term x y := by
    intro x y
    dsimp [term,EdgeMixing.chi]
    split_ifs <;> simp_all [linkEdge_nonneg hw]
  have hpoint (a : Finset V) : (if Collision F s a then w a else 0) ≤
      ∑ x : V, ∑ y : V, if a = insert x (insert y s) then term x y else 0 := by
    by_cases hc : Collision F s a
    · rw [ite_eq_left hc]
      obtain ⟨x,y,hx,hy,hxy,hrep,hFx,hFy⟩ := hc.reconstruct
      have hv : (if a = insert x (insert y s) then term x y else 0) = w a := by
        simp [hrep,term,EdgeMixing.chi,hFx,hFy,linkEdge,hx,hy,hxy]
      rw [←hv]
      apply (Finset.single_le_sum (fun y _ => by split_ifs; exact ht x y; rfl)
        (Finset.mem_univ y)).trans
      apply Finset.single_le_sum _ (Finset.mem_univ x)
      intro u _
      exact Finset.sum_nonneg (fun v _ => by split_ifs; exact ht u v; rfl)
    · rw [ite_eq_right hc]
      exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => by
        split_ifs; exact ht x y; rfl))
  calc
    collisionMass w F s ≤ ∑ a ∈ level (s.card+2),
      ∑ x : V, ∑ y : V, if a = insert x (insert y s) then term x y else 0 :=
        Finset.sum_le_sum (fun a _ => hpoint a)
    _ = ∑ x : V, ∑ y : V, ∑ a ∈ level (s.card+2),
        if a = insert x (insert y s) then term x y else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ ≤ ∑ x : V, ∑ y : V, term x y := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      simp only [Finset.sum_ite_eq']
      split_ifs
      · rfl
      · exact ht x y
    _ = _ := rfl

theorem localMixing_of_rayleigh {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hray : ∀ s : Finset V, s.card+2 ≤ N → 0 < w s → EdgeMixing.Rayleigh (linkEdge w s) lam) :
    LocalMixing w N lam := by
  intro F s hs t ht hsmall
  have hnon : 0 ≤ (t+lam)*(N:ℝ)*starNorm w (s.card+1) s (indicator F) :=
    mul_nonneg (mul_nonneg (add_nonneg ht hlam) (Nat.cast_nonneg _))
      (starNorm_nonneg hw.nonneg _ _ _)
  by_cases hr : s.card+2 ≤ N
  · by_cases hpos : 0 < w s
    · have hcpos : (0:ℝ) < (N-s.card-1:ℕ) := by exact_mod_cast (show 0 < N-s.card-1 by omega)
      have hvpos : 0 < EdgeMixing.volume (linkEdge w s) := by
        rw [linkEdge_volume hw]
        exact mul_pos (mul_pos hcpos (by exact_mod_cast (show 0 < N-s.card by omega))) hpos
      have hm : EdgeMixing.selected (linkEdge w s) (fun x => F (insert x s)) ≤
          t*EdgeMixing.volume (linkEdge w s) := by
        rw [linkEdge_selected hw,linkEdge_volume hw]
        nlinarith [mul_le_mul_of_nonneg_left hsmall hcpos.le]
      have hh := EdgeMixing.small_set (linkEdge w s) (linkEdge_nonneg hw.nonneg s)
        (linkEdge_symm w s) hvpos hlam (hray s hr hpos) (fun x => F (insert x s)) hm
      apply (collision_le_pairing hw.nonneg F s).trans
      apply hh.trans
      rw [linkEdge_selected hw]
      have hcN : (N-s.card-1:ℕ) ≤ N := by omega
      have hcr : ((N-s.card-1:ℕ):ℝ) ≤ N := by exact_mod_cast hcN
      have hn := starNorm_nonneg hw.nonneg (s.card+1) s (indicator F)
      nlinarith [mul_le_mul_of_nonneg_right hcr (mul_nonneg (add_nonneg ht hlam) hn)]
    · have hz : w s = 0 := le_antisymm (le_of_not_gt hpos) (hw.nonneg s)
      have hzero : collisionMass w F s = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        split_ifs with hc
        · obtain ⟨x,y,hx,hy,hxy,hrep,hFx,hFy⟩ := hc.reconstruct
          exact hw.weight_eq_zero_of_base (hrep ▸
            (Finset.subset_insert y s).trans (Finset.subset_insert x (insert y s))) hz
        · rfl
      rw [hzero]
      exact hnon
  · have hzero : collisionMass w F s = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hah := mem_level.mp ha
      split_ifs
      · exact hw.vanish a (by omega)
      · rfl
    rw [hzero]
    exact hnon

end CoboundaryExpanders.FatLadders

end

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.EdgeMixing

section
variable {V W : Type} [Fintype V] [Fintype W]
attribute [local instance] Classical.propDecidable

lemma active_action (e : V → V → ℝ) (he : ∀ x y,0 ≤ e x y)
    (hs : ∀ x y,e x y = e y x) (f : Active e → ℝ) (x : Active e) :
    action e ((activeEmbedding e he).extend f) x.val = (activeGraph e he hs).action f x := by
  let M := activeEmbedding e he
  change (∑ y,e x.val y*M.extend f y)/mass e x.val =
    (∑ y : Active e,e x.val y.val*f y)/(activeGraph e he hs).mass x
  have hz (y : V) (hy : y ∉ Set.range M.vertex) : e x.val y*M.extend f y = 0 := by
    rw [hs,M.outside_zero y hy,zero_mul]
  rw [sum_embedding M.vertex M.injective _ hz]
  have hm := M.mass_map hs x
  change mass e x.val = (activeGraph e he hs).mass x at hm
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [M.extend_map]
  rfl

theorem trickle {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) (hs : ∀ x y,e x y = e y x)
    (hc : Connected e) {lam : ℝ} (hlam : lam < 1)
    (hloc : ∀ f : V → ℝ, pairing e f f ≤ lam*energy e f+(1-lam)*energy e (action e f)) :
    Rayleigh e (lam/(1-lam)) := by
  let M := activeEmbedding e he
  by_cases hne : Nonempty (Active e)
  · let := hne
    let G := activeGraph e he hs
    apply M.push hs
    intro f hf
    change G.pairing f f ≤ (lam/(1-lam))*G.energy f
    apply G.trickle hc hlam _ f hf
    intro g
    have h := hloc (M.extend g)
    rw [M.pairing_pull hs,M.energy_pull hs,M.extend_comp,M.energy_pull hs] at h
    have hg : action e (M.extend g) ∘ M.vertex = G.action g := by
      funext x
      exact active_action e he hs g x
    rw [hg] at h
    exact h
  · have hzero (x y : V) : e x y = 0 :=
      M.outside_zero x (by rintro ⟨z,hz⟩; exact hne ⟨z⟩) y
    intro f hf
    simp only [pairing,energy,mass,hzero,zero_mul,Finset.sum_const_zero,mul_zero,le_refl]

end

variable {V : Type} [Fintype V]
lemma energy_sub_const (e : V → V → ℝ) (f : V → ℝ) (a : ℝ) :
    energy e (fun x => f x-a) = energy e f - 2*a*(∑ x,mass e x*f x)+a^2*(∑ x,mass e x) := by
  simp only [energy,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring
lemma pairing_sub_const (e : V → V → ℝ) (hs : ∀ x y,e x y = e y x)
    (f : V → ℝ) (a : ℝ) :
    pairing e (fun x => f x-a) (fun x => f x-a) =
      pairing e f f - 2*a*(∑ x,mass e x*f x)+a^2*(∑ x,mass e x) := by
  have he : pairing e (fun x => f x-a) (fun x => f x-a) = pairing e f f -
      a*(∑ x,∑ y,e x y*f x)-a*(∑ x,∑ y,e x y*f y)+a^2*(∑ x,mass e x) := by
    simp only [pairing,mass,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hr : (∑ x,∑ y,e x y*f y) = ∑ x,mass e x*f x := by
    rw [Finset.sum_comm]
    simp only [mass,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hs]
  rw [he,hr]
  simp only [←Finset.sum_mul]
  change pairing e f f-a*(∑x,mass e x*f x)-a*(∑x,mass e x*f x)+_ = _
  ring

lemma centered_bound {e : V → V → ℝ} (hs : ∀ x y,e x y = e y x)
    {lam : ℝ} (h : Rayleigh e lam) (f : V → ℝ) (a : ℝ)
    (ha : (∑ x,mass e x*f x) = (∑ x,mass e x)*a) :
    pairing e f f ≤ lam*energy e f+(1-lam)*(∑ x,mass e x)*a^2 := by
  have hz : (∑ x,mass e x*(f x-a)) = 0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    rw [ha]; ring
  have hh := h (fun x => f x-a) hz
  rw [energy_sub_const,pairing_sub_const e hs,ha] at hh
  nlinarith [hh]

lemma mass_mul_action {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) (f : V → ℝ) (x : V) :
    mass e x * action e f x = ∑y,e x y*f y := by
  by_cases hx : mass e x = 0
  · have hz (y : V) : e x y = 0 := edge_zero_of_nonactive he (by rw [hx]; exact lt_irrefl _) y
    simp [hx,hz]
  · exact mul_div_cancel₀ _ hx

theorem triangle_moment {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y)
    (hs : ∀ x y,e x y = e y x) (d : V → V → V → ℝ)
    (hd : ∀ x y z,d x y z = d x z y) {c : ℝ} (hc : 0 < c)
    (hm : ∀ x y,mass (d x) y = c*e x y)
    (ht : ∀ y z,(∑ x,d x y z) = c*e y z)
    {lam : ℝ} (hr : ∀ x,Rayleigh (d x) lam) (f : V → ℝ) :
    pairing e f f ≤ lam*energy e f+(1-lam)*energy e (action e f) := by
  have hl (x : V) : pairing (d x) f f ≤ lam*energy (d x) f+
      (1-lam)*c*mass e x*(action e f x)^2 := by
    have hv : (∑y,mass (d x) y) = c*mass e x := by
      simp only [hm]
      rw [←Finset.mul_sum]
      rfl
    have hmean : (∑y,mass (d x) y*f y) = (∑y,mass (d x) y)*action e f x := by
      rw [hv]
      simp only [hm,mul_assoc,←Finset.mul_sum,mass_mul_action he]
    have h := centered_bound (hd x) (hr x) f (action e f x) hmean
    simpa only [hv,mul_assoc] using h
  have hp : (∑x,pairing (d x) f f) = c*pairing e f f := by
    simp only [pairing]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun x z => d x _ z*f _*f z)]
    simp only [←Finset.sum_mul,ht,Finset.mul_sum,mul_assoc]
  have hen : (∑x,energy (d x) f) = c*energy e f := by
    simp only [energy,hm]
    rw [Finset.sum_comm]
    simp only [←Finset.sum_mul,←Finset.mul_sum]
    unfold mass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [show (∑x,e x y) = ∑x,e y x by apply Finset.sum_congr rfl; intro x _; rw [hs]]
    ring
  have ha : (∑x,(1-lam)*c*mass e x*(action e f x)^2) =
      c*(1-lam)*energy e (action e f) := by
    simp only [energy,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => hl x)
  rw [hp,Finset.sum_add_distrib,←Finset.mul_sum,hen,ha] at h
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith [h]

theorem triangle_trickle {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y)
    (hs : ∀ x y,e x y = e y x) (hconn : Connected e) (d : V → V → V → ℝ)
    (hd : ∀ x y z,d x y z = d x z y) {c : ℝ} (hc : 0 < c)
    (hm : ∀ x y,mass (d x) y = c*e x y)
    (ht : ∀ y z,(∑ x,d x y z) = c*e y z)
    {lam : ℝ} (hlam : lam < 1) (hr : ∀ x,Rayleigh (d x) lam) :
    Rayleigh e (lam/(1-lam)) :=
  trickle he hs hconn hlam (triangle_moment he hs d hd hc hm ht hr)
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.FatLadders

section
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
lemma triangle_cycle (w : Finset V → ℝ) (s : Finset V) (x y z : V) :
    triangle w s x y z = triangle w s y z x := by
  unfold triangle linkEdge
  simp only [Finset.mem_insert]
  split_ifs <;> simp_all [Finset.insert_comm,ne_comm]
omit [Fintype V] in
lemma triangle_symm (w : Finset V → ℝ) (s : Finset V) (x y z : V) :
    triangle w s x y z = triangle w s x z y := by
  unfold triangle
  rw [linkEdge_symm]
lemma triangle_mass {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (x y : V) :
    EdgeMixing.mass (triangle w s x) y = (N-s.card-2:ℕ)*linkEdge w s x y := by
  by_cases hx : x ∈ s
  · simp [EdgeMixing.mass,triangle,linkEdge,hx]
  · have he : triangle w s x = linkEdge w (insert x s) := by funext a b; simp [triangle,hx]
    rw [he,linkEdge_mass hw,Finset.card_insert_of_notMem hx]
    have hnat : N-(s.card+1)-1 = N-s.card-2 := by omega
    rw [hnat]
    by_cases hy : y ∈ s
    · simp [linkEdge,hy]
    · by_cases hxy : x = y
      · subst y; simp [linkEdge]
      · simp [linkEdge,hx,hy,hxy,Ne.symm hxy,Finset.insert_comm]
lemma triangle_sum {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (y z : V) :
    (∑x,triangle w s x y z) = (N-s.card-2:ℕ)*linkEdge w s y z := by
  simp_rw [triangle_cycle w s _ y z]
  exact triangle_mass hw s y z
lemma linkEdge_zero {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {s : Finset V} (hz : w s = 0) : linkEdge w s = 0 := by
  funext x y
  unfold linkEdge
  split_ifs
  · exact hw.weight_eq_zero_of_base ((Finset.subset_insert y s).trans (Finset.subset_insert x _)) hz
  · rfl

theorem link_trickle {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (hrank : s.card+3 ≤ N)
    (hc : EdgeMixing.Connected (linkEdge w s)) {lam : ℝ} (hlam : lam < 1)
    (hray : ∀ x, x ∉ s → 0 < w (insert x s) →
      EdgeMixing.Rayleigh (linkEdge w (insert x s)) lam) :
    EdgeMixing.Rayleigh (linkEdge w s) (lam/(1-lam)) := by
  apply EdgeMixing.triangle_trickle (linkEdge_nonneg hw.nonneg s) (linkEdge_symm w s) hc
    (triangle w s) (triangle_symm w s) (by exact_mod_cast (show 0 < N-s.card-2 by omega))
    (triangle_mass hw s) (triangle_sum hw s) hlam
  intro x
  by_cases hx : x ∈ s
  · intro f hf
    simp [EdgeMixing.pairing,EdgeMixing.energy,EdgeMixing.mass,triangle,hx]
  · have he : triangle w s x = linkEdge w (insert x s) := by funext a b; simp [triangle,hx]
    rw [he]
    by_cases hp : 0 < w (insert x s)
    · exact hray x hx hp
    · have hz : w (insert x s) = 0 := le_antisymm (not_lt.mp hp) (hw.nonneg _)
      rw [linkEdge_zero hw hz]
      intro f hf
      simp [EdgeMixing.pairing,EdgeMixing.energy,EdgeMixing.mass]
end

variable {V : Type} [Fintype V] [DecidableEq V]
theorem link_trickle_double {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (hrank : s.card+3 ≤ N)
    (hc : EdgeMixing.Connected (linkEdge w s)) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hray : ∀ x, x ∉ s → 0 < w (insert x s) →
      EdgeMixing.Rayleigh (linkEdge w (insert x s)) (lam/2)) :
    EdgeMixing.Rayleigh (linkEdge w s) lam := by
  apply EdgeMixing.rayleigh_mono (linkEdge_nonneg hw.nonneg s) (link_trickle hw s hrank hc (by linarith) hray)
  apply (div_le_iff₀ (by linarith : 0 < 1-lam/2)).mpr
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

theorem all_link_rayleigh {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (hc : ∀ s : Finset V, s.card+3 ≤ N → 0 < w s → EdgeMixing.Connected (linkEdge w s))
    (htop : ∀ s : Finset V, s.card+2 = N → 0 < w s →
      EdgeMixing.Rayleigh (linkEdge w s) (eps / 2^(N-2))) :
    ∀ s : Finset V, s.card+2 ≤ N → 0 < w s → EdgeMixing.Rayleigh (linkEdge w s) eps := by
  have main : ∀ r : ℕ, ∀ s : Finset V, N-s.card = r → s.card+2 ≤ N → 0 < w s →
      EdgeMixing.Rayleigh (linkEdge w s) (eps / 2^s.card) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro s heq hr hs
      by_cases ht : s.card+2 = N
      · have hcard : s.card = N-2 := by omega
        simpa only [hcard] using htop s ht hs
      · have hr3 : s.card+3 ≤ N := by omega
        have hp : (1:ℝ) ≤ 2^s.card := one_le_pow₀ (by norm_num)
        apply link_trickle_double hw s hr3 (hc s hr3 hs) (div_nonneg h0 (by positivity))
          ((div_le_self h0 hp).trans h1)
        intro x hx hxp
        have hc' : (insert x s).card = s.card+1 := Finset.card_insert_of_notMem hx
        have hi : N-(insert x s).card < r := by rw [hc']; omega
        have hh := ih (N-(insert x s).card) hi (insert x s) rfl (by rw [hc']; omega) hxp
        simpa only [hc',pow_succ,div_mul_eq_div_div] using hh
  intro s hr hs
  apply EdgeMixing.rayleigh_mono (linkEdge_nonneg hw.nonneg s) (main _ s rfl hr hs)
  exact div_le_self h0 (one_le_pow₀ (by norm_num))
end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.InfiniteChains.FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable
lemma cofaces_chamberWeight (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) :
    FatLadders.chamberWeight (fun t : ↥(level X N) => t.val) (fun _ => (1:ℝ)) =
      fun s => (cofaces X N s : ℝ) := by
  funext s
  unfold FatLadders.chamberWeight cofaces
  dsimp only
  calc
    _ = ∑ t ∈ level X N, if s ⊆ t then (1:ℝ) else 0 :=
      Finset.sum_coe_sort (level X N) (fun t => if s ⊆ t then (1:ℝ) else 0)
    _ = _ := Finset.sum_boole _ _

lemma cofaces_balanced (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) :
    FatLadders.Balanced (fun s => (cofaces X N s : ℝ)) N := by
  rw [←cofaces_chamberWeight X N]
  exact FatLadders.chamberWeight_balanced _ _ N
    (fun t => ((mem_level X N t.val).mp t.property).2) (fun _ => by norm_num)

lemma linkEdge_eq (X : CoboundaryExpanders.InfiniteChains.Complex V) {N : ℕ} {s : Finset V} (hs : s ∈ X.faces)
    (hN : s.card ≤ N) :
    FatLadders.linkEdge (fun t => (cofaces X N t : ℝ)) s = edge (X.faceLink s hs) (N-s.card) := by
  funext x y
  by_cases hx : x ∈ s
  · have hf : ({x}:Finset V) ∉ (X.faceLink s hs).faces := by
      intro h
      exact Finset.disjoint_left.mp h.1 hx (Finset.mem_singleton_self x)
    simp [FatLadders.linkEdge,hx,edge_zero_of_not_face _ _ hf]
  by_cases hy : y ∈ s
  · have hf : ({y}:Finset V) ∉ (X.faceLink s hs).faces := by
      intro h
      exact Finset.disjoint_left.mp h.1 hy (Finset.mem_singleton_self y)
    rw [edge_symm _ _ x y,edge_zero_of_not_face _ _ hf]
    simp [FatLadders.linkEdge,hy]
  have hd : Disjoint s {x,y} := by simp [hx,hy]
  simp only [FatLadders.linkEdge,hx,hy,not_false_eq_true,true_and,edge]
  split_ifs
  · rw [cofaces_link X hs hN hd]
    congr 2
    ext z
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  · rfl
end CoboundaryExpanders.InfiniteChains.FiniteWeights

namespace CoboundaryExpanders.InfiniteChains
open Cone FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]
lemma FiniteWeights.active_face (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (x : V)
    (hx : 0 < EdgeMixing.mass (edge X N) x) : ({x}:Finset V) ∈ X.faces := by
  by_contra h
  have hz : EdgeMixing.mass (edge X N) x = 0 := by
    simp only [EdgeMixing.mass,edge_zero_of_not_face X N h,Finset.sum_const_zero]
  rw [hz] at hx
  exact (lt_irrefl _) hx
lemma FiniteWeights.edge_pos {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) {x y : V}
    (hxy : x ≠ y) (hface : ({x,y}:Finset V) ∈ X.faces) : 0 < edge X N x y := by
  rw [edge,ite_eq_left hxy]
  exact_mod_cast cofaces_pos hP hface

lemma Cone.VertexPath.toActive {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) {x y : V}
    (hpath : VertexPath X x y) (hx : 0 < EdgeMixing.mass (edge X N) x)
    (hy : 0 < EdgeMixing.mass (edge X N) y) :
    Relation.ReflTransGen (fun a b : EdgeMixing.Active (edge X N) => 0 < edge X N a.val b.val)
      ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hpath hbc ih =>
    by_cases he : b = c
    · subst c
      exact ih hy
    · have hp := edge_pos hP he hbc
      have hb : 0 < EdgeMixing.mass (edge X N) b := hp.trans_le (EdgeMixing.edge_le_mass (edge_nonneg X N) b c)
      exact (ih hb).tail hp

theorem Cone.BoundedCone.spectralConnected {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R N : ℕ}
    (H : BoundedCone X n R) (hn : 1 ≤ n) (hP : Pure X N) :
    EdgeMixing.Connected (edge X N) := by
  intro x y
  exact (H.vertexPath hn x.val y.val (active_face X N x.val x.property)
    (active_face X N y.val y.property)).toActive hP x.property y.property
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains InfiniteChains.Cone InfiniteChains.FiniteWeights
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma spectralConnected_of_generate [Fintype (Vertex H)] {N : ℕ} (hp : Pure (complex H) N)
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) (base : I) :
    EdgeMixing.Connected (edge (complex H) N) := by
  intro x y
  exact (vertexPath_of_generate H hgen base x.val y.val).toActive hp x.property y.property
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction

section
open Elementary
variable (p n : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem cycleRoot_mem_generated (hn : 1 ≤ n) (j : Fin (n + 1)) :
    cycleRoot p n hn j ∈ cycleGenerated p n hn :=
  Subgroup.subset_closure ⟨j, rfl⟩

theorem cycleGenerated_le_U (hn : 1 ≤ n) : cycleGenerated p n hn ≤ U p (n + 1) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact cycleRoot_mem_U p n hn j

omit [Fact p.Prime] in
theorem upper_adjacent_mem_generated (hn : 1 ≤ n) (i j : Fin (n + 1))
    (hij : i.val + 1 = j.val) :
    E (show i ≠ j by intro he; subst j; omega) (1 : R p) ∈ cycleGenerated p n hn := by
  have hj : j ≠ 0 := by intro he; subst j; simp at hij
  have hs : edgeSource n j = i := by
    apply Fin.ext
    simp only [edgeSource, dite_eq_right hj, Fin.val_mk]
    omega
  simpa only [cycleRoot, ite_eq_right hj, hs] using cycleRoot_mem_generated p n hn j

omit [Fact p.Prime] in
theorem upper_one_mem_generated (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : i < j) :
    E hij.ne (1 : R p) ∈ cycleGenerated p n hn :=
  E_upper_one_mem _ (upper_adjacent_mem_generated p n hn) hij

omit [Fact p.Prime] in
theorem lower_X_mem_generated (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : j < i) :
    E hij.ne.symm (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
  have hlast0 : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  have hbase : E hlast0 (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
    simpa [cycleRoot, edgeSource, E] using
      cycleRoot_mem_generated p n hn 0
  have hlastj : j < Fin.last n := by change j.val < n; have := i.isLt; omega
  have hlast : E hlastj.ne.symm (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
    by_cases hj : j = 0
    · subst j; exact hbase
    · have h0j : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj
      simpa only [mul_one] using E_path_mem (cycleGenerated p n hn)
        hlast0 h0j.ne hlastj.ne.symm hbase (upper_one_mem_generated p n hn h0j)
  by_cases hi : i = Fin.last n
  · subst i; exact hlast
  · have hilast : i < Fin.last n := by change i.val < n; have := i.isLt; have := Fin.ext_iff.not.mp hi; simp only [Fin.val_last] at this; omega
    simpa only [one_mul] using E_path_mem (cycleGenerated p n hn)
      hilast.ne hlastj.ne.symm hij.ne.symm (upper_one_mem_generated p n hn hilast) hlast

omit [Fact p.Prime] in
theorem X_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j) :
    E hij (Polynomial.X : R p) ∈ cycleGenerated p n (by omega) := by
  have hn1 : 1 ≤ n := by omega
  by_cases hji : j < i
  · exact lower_X_mem_generated p n hn1 hji
  have hij' : i < j := lt_of_le_of_ne (le_of_not_gt hji) hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = Fin.last n
    · subst j
      let k : Fin (n + 1) := ⟨1, by omega⟩
      have h0k : (0 : Fin (n + 1)) < k := by change (0 : ℕ) < 1; omega
      have hklast : k < Fin.last n := by change 1 < n; omega
      have hk0 := lower_X_mem_generated p n hn1 h0k
      have h0last := upper_one_mem_generated p n hn1 hij'
      have hklastX : E hklast.ne (Polynomial.X : R p) ∈ cycleGenerated p n hn1 := by
        simpa only [mul_one] using E_path_mem (cycleGenerated p n hn1)
          h0k.ne.symm hij'.ne hklast.ne hk0 h0last
      simpa only [one_mul] using E_path_mem (cycleGenerated p n hn1)
        h0k.ne hklast.ne hij (upper_one_mem_generated p n hn1 h0k) hklastX
    · have hjlast : j < Fin.last n := by
        change j.val < n
        have := j.isLt
        have := Fin.ext_iff.not.mp hj
        simp only [Fin.val_last] at this
        omega
      have h0last : (0 : Fin (n + 1)) < Fin.last n := by change 0 < n; omega
      simpa only [one_mul] using E_path_mem (cycleGenerated p n hn1)
        h0last.ne hjlast.ne.symm hij (upper_one_mem_generated p n hn1 h0last)
        (lower_X_mem_generated p n hn1 hjlast)
  · have h0i : (0 : Fin (n + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
    have h0j : (0 : Fin (n + 1)) < j := h0i.trans hij'
    simpa only [mul_one] using E_path_mem (cycleGenerated p n hn1)
      h0i.ne.symm h0j.ne hij (lower_X_mem_generated p n hn1 h0i)
      (upper_one_mem_generated p n hn1 h0j)

omit [Fact p.Prime] in
theorem X_pow_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j) (r : ℕ) :
    E hij (Polynomial.X ^ (r + 1) : R p) ∈ cycleGenerated p n (by omega) := by
  induction r generalizing i j with
  | zero => simpa only [zero_add, pow_one] using X_mem_generated p n hn hij
  | succ r ih =>
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    simpa only [pow_succ] using E_path_mem (cycleGenerated p n (by omega))
      hki.symm hkj hij (ih hki.symm) (X_mem_generated p n hn hkj)

theorem scalar_root_mem (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j)
    {f : R p} (hf : E hij f ∈ cycleGenerated p n hn) (c : ZMod p) :
    E hij (Polynomial.C c * f) ∈ cycleGenerated p n hn := by
  have hc : Polynomial.C c = (c.val : R p) := by
    calc Polynomial.C c = Polynomial.C (c.val : ZMod p) :=
           congrArg Polynomial.C (ZMod.natCast_zmod_val c).symm
         _ = _ := map_natCast Polynomial.C _
  rw [hc, E_natCast_mul]
  exact (cycleGenerated p n hn).pow_mem hf _

theorem upper_polynomial_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)}
    (hij : i < j) (f : R p) : E hij.ne f ∈ cycleGenerated p n (by omega) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    change Matrix.SpecialLinearGroup.transvection hij.ne (f + g) ∈ _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact (cycleGenerated p n (by omega)).mul_mem hf hg
  | monomial r c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    apply scalar_root_mem
    cases r with
    | zero => simpa using upper_one_mem_generated p n (by omega) hij
    | succ r => exact X_pow_mem_generated p n hn hij.ne r

theorem X_polynomial_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)}
    (hij : i ≠ j) (f : R p) :
    E hij (Polynomial.X * f) ∈ cycleGenerated p n (by omega) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [mul_add]
    change Matrix.SpecialLinearGroup.transvection hij (_ + _) ∈ _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact (cycleGenerated p n (by omega)).mul_mem hf hg
  | monomial r c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [mul_left_comm, ← pow_succ']
    exact scalar_root_mem p n (by omega) hij (X_pow_mem_generated p n hn hij r) c

end

open Elementary
variable (p n m : ℕ) [Fact p.Prime]

theorem map_E {A B : Type*} [CommRing A] [CommRing B] {a : ℕ}
    (φ : A →+* B) {i j : Fin a} (hij : i ≠ j) (c : A) :
    Matrix.SpecialLinearGroup.map φ (E hij c) = E hij (φ c) := by
  exact map_transvection φ hij c

theorem truncatedIwahori_entries (hm : 1 ≤ m)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m))
    (hg : g ∈ truncatedIwahori p n m hm) (i j : Fin (n + 1)) (hji : j ≤ i) :
    residue p m hm (g i j) = if i = j then 1 else 0 := by
  have := hg i j hji
  simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.one_apply] using this

theorem reduction_mem_truncatedIwahori (hm : 1 ≤ m)
    {g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)} (hg : g ∈ U p (n + 1)) :
    Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) g ∈
      truncatedIwahori p n m hm := by
  intro i j hji
  have := hg i j hji
  simpa [evalZero, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] using this

theorem reducedGenerated_le (hn : 1 ≤ n) (hm : 1 ≤ m) :
    reducedGenerated p n m hn ≤ truncatedIwahori p n m hm := by
  rintro _ ⟨g, hg, rfl⟩
  exact reduction_mem_truncatedIwahori p n m hm (cycleGenerated_le_U p n hn hg)

theorem reducedGenerated_roots (hn : 2 ≤ n) (hm : 1 ≤ m)
    (i j : Fin (n + 1)) (hij : i ≠ j) (c : Trunc p m)
    (hc : j < i → residue p m hm c = 0) :
    E hij c ∈ reducedGenerated p n m (by omega) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨E hij f, ?_, map_E _ hij f⟩
  by_cases hji : j < i
  · have hf : Polynomial.X ∣ f := Polynomial.X_dvd_iff.mpr (by
      have := hc hji
      simpa [Polynomial.coeff_zero_eq_eval_zero] using this)
    obtain ⟨b, rfl⟩ := hf
    exact X_polynomial_mem_generated p n hn hij b
  · exact upper_polynomial_mem_generated p n hn (lt_of_le_of_ne (le_of_not_gt hji) hij) f

theorem truncatedIwahori_eq_generated (hn : 2 ≤ n) (hm : 1 ≤ m) :
    truncatedIwahori p n m hm = reducedGenerated p n m (by omega) := by
  apply le_antisymm
  · exact iwahori_mem_of_roots (residue p m hm) _ _
      (reducedGenerated_le p n m (by omega) hm)
      (truncatedIwahori_entries p n m hm) (residue_one_isUnit p m hm)
      (reducedGenerated_roots p n m hn hm)
  · exact reducedGenerated_le p n m (by omega) hm

theorem quotient_locals_generate (hn : 2 ≤ n) (hm : 1 ≤ m) :
    Subgroup.closure (⋃ i, (reducedLocalGroup p n (by omega) m i : Set (Gquot p (n + 1) m))) = ⊤ := by
  let K : Subgroup (Gquot p (n + 1) m) :=
    Subgroup.closure (⋃ i, (reducedLocalGroup p n (by omega) m i : Set (Gquot p (n + 1) m)))
  let e : Gquot p (n + 1) m →* Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m) :=
    QuotientGroup.kerLift (uReduction p (n + 1) m)
  have he : Function.Injective e := QuotientGroup.kerLift_injective _
  have hgen : reducedGenerated p n m (by omega) ≤ K.map e := by
    apply (Subgroup.map_le_iff_le_comap).mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨cut, hcut⟩ : ∃ cut : Fin (n + 1), cut ≠ j := by
      by_cases hj : j = 0
      · refine ⟨Fin.last n, ?_⟩
        rw [hj]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_zero] at this
        omega
      · exact ⟨0, fun h => hj h.symm⟩
    let u : U p (n + 1) := ⟨cycleRoot p n (by omega) j, cycleRoot_mem_U p n (by omega) j⟩
    have hu : u ∈ uLocalGroup p n (by omega) cut :=
      Subgroup.subset_closure ⟨j, hcut.symm, rfl⟩
    have hq : QuotientGroup.mk' (uReduction p (n + 1) m).ker u ∈ K :=
      Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨cut, ⟨u, hu, rfl⟩⟩)
    exact ⟨_, hq, rfl⟩
  apply top_le_iff.mp
  intro q _
  induction q using QuotientGroup.induction_on with
  | H u =>
    have hu := reduction_mem_truncatedIwahori p n m hm u.property
    rw [truncatedIwahori_eq_generated p n m hn hm] at hu
    obtain ⟨v, hv, hev⟩ := hgen hu
    have hveq : v = QuotientGroup.mk u := he hev
    exact hveq ▸ hv

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders
lemma sqrt_div_le_of_sq {p t : ℝ} (hp : 0 < p) (ht : 0 < t) (h : 1 ≤ t^2*p) :
    Real.sqrt p/p ≤ t := by
  have hs := Real.sqrt_nonneg p
  have he := Real.sq_sqrt hp.le
  have hsq : 1 ≤ (t*Real.sqrt p)^2 := by simpa only [mul_pow,he] using h
  have hpos : 0 ≤ t*Real.sqrt p := mul_nonneg ht.le hs
  have hb : 1 ≤ t*Real.sqrt p := by nlinarith
  apply (div_le_iff₀ hp).mpr
  calc
    Real.sqrt p = 1*Real.sqrt p := by ring
    _ ≤ (t*Real.sqrt p)*Real.sqrt p := mul_le_mul_of_nonneg_right hb hs
    _ = t*p := by nlinarith [mul_assoc t (Real.sqrt p) (Real.sqrt p)]

theorem exists_spectral_threshold (r : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ Q : ℕ, ∀ p : ℕ, Q < p → Real.sqrt (p:ℝ)/(p:ℝ) ≤ eps/(2:ℝ)^r := by
  let t := eps/(2:ℝ)^r
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨Q,hQ⟩ := exists_nat_gt (1/t^2)
  refine ⟨Q,?_⟩
  intro p hp
  have hp' : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hb : 1/t^2 ≤ (p:ℝ) := hQ.le.trans (by exact_mod_cast hp.le)
  have hc : 1 ≤ t^2*(p:ℝ) := by
    have h := (div_le_iff₀ (sq_pos_of_pos ht)).mp hb
    simpa only [mul_comm] using h
  exact sqrt_div_le_of_sq hp' ht hc
end CoboundaryExpanders

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains FiniteWeights Cone
open scoped Pointwise
variable {G I : Type} [Group G] [Fintype G] [DecidableEq I] [Fintype I] (H : I → Subgroup G)

lemma finite_pure : Pure (complex H) (Fintype.card I) := by
  obtain ⟨hne,h⟩ := coset_pure H
  constructor
  · obtain ⟨t,ht,he⟩ := hne
    exact ⟨t,(mem_level _ _ _).mpr ⟨ht,he⟩⟩
  · intro s hs
    obtain ⟨t,ht,he,hst⟩ := h s hs
    exact ⟨t,(mem_level _ _ _).mpr ⟨ht,he⟩,hst⟩

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.InfiniteChains
open Cone FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]

lemma FiniteWeights.linkEdge_empty (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) :
    FatLadders.linkEdge (fun t => (cofaces X N t : ℝ)) ∅ = edge X N := by
  funext x y
  simp [FatLadders.linkEdge,edge]

lemma TopSpectral.changeFintype {V : Type} [DecidableEq V] {fa : Fintype V}
    (fb : Fintype V) {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} {lam : ℝ}
    (ht : @TopSpectral V fa _ X N lam) : @TopSpectral V fb _ X N lam := by
  cases Subsingleton.elim fa fb
  exact ht

theorem mixing_of_top_cones {X : CoboundaryExpanders.InfiniteChains.Complex V} {N R : ℕ} (hp : Pure X N)
    (hc : EdgeMixing.Connected (edge X N)) (hcones : ProperLinkCones X N R)
    {eps lam : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (htop : TopSpectral X N lam) (hlam : lam ≤ eps/2^(N-2)) :
    FatLadders.LocalMixing (fun t => (cofaces X N t : ℝ)) N eps := by
  apply FatLadders.localMixing_of_rayleigh (cofaces_balanced X N) h0
  apply FatLadders.all_link_rayleigh (cofaces_balanced X N) h0 h1
  · intro s hr hs
    have hs' : s ∈ X.faces := (cofaces_pos_iff hp s).mp (by exact_mod_cast hs)
    by_cases he : s.Nonempty
    · rw [linkEdge_eq X hs' (by omega)]
      exact (hcones s he hs' (by omega)).some.spectralConnected (by omega) (pure_link hp hs')
    · have he' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      subst s
      rwa [linkEdge_empty X N]
  · intro s hr hs
    have hs' : s ∈ X.faces := (cofaces_pos_iff hp s).mp (by exact_mod_cast hs)
    rw [linkEdge_eq X hs' (by omega)]
    have he : N-s.card = 2 := by omega
    rw [he]
    exact EdgeMixing.rayleigh_mono (edge_nonneg _ _) (htop s hs' hr) hlam
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone FiniteWeights
variable {G I : Type} [Group G] [Fintype G] [DecidableEq I] [Fintype I]
lemma coset_mixing (H : I → Subgroup G) {N R : ℕ} (hN : Fintype.card I = N)
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) (base : I)
    {eps lam : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (hcones : ProperLinkCones (complex H) N R) (ht : TopSpectral (complex H) N lam)
    (hlam : lam ≤ eps / 2^(N-2)) :
    FatLadders.LocalMixing (fun t => (cofaces (complex H) N t : ℝ)) N eps := by
  have hP : Pure (complex H) N := hN ▸ finite_pure H
  exact mixing_of_top_cones hP (spectralConnected_of_generate H hP hgen base)
    hcones h0 h1 ht hlam
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open InfiniteChains Cone FiniteWeights TypedCosetFaces

lemma actual_mixing_level (n : ℕ) (hn : 2 ≤ n) (p : ℕ) [Fact p.Prime]
    (m : ℕ) (hm : 2 ≤ m) {R : ℕ} {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (hcones : ProperLinkCones (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1) R)
    (hlam : Real.sqrt p / p ≤ eps / 2^(n+1-2)) :
    letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
    FatLadders.LocalMixing
      (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1) t : ℝ)) (n+1) eps := by
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  have htop := actual_topSpectral n hn p m hm
  have ht := TopSpectral.changeFintype (vertexFintype (reducedLocalGroup p n (by omega) m)) htop
  exact coset_mixing (reducedLocalGroup p n (by omega) m) (Fintype.card_fin _)
    (quotient_locals_generate p n m hn (by omega)) 0 h0 h1 hcones
    ht hlam

lemma actual_mixing_mono (n : ℕ) (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime] (m : ℕ)
    {eps mu : ℝ} (h : eps ≤ mu) :
    letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
    FatLadders.LocalMixing
      (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n hn m)) (n+1) t : ℝ)) (n+1) eps →
    FatLadders.LocalMixing
      (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n hn m)) (n+1) t : ℝ)) (n+1) mu := by
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  intro hmix F s hs t ht hb
  apply (hmix F s hs t ht hb).trans
  apply mul_le_mul_of_nonneg_right _ (FatLadders.starNorm_nonneg (fun s => Nat.cast_nonneg _) _ _ _)
  exact mul_le_mul_of_nonneg_right (add_le_add_right h t) (Nat.cast_nonneg _)

theorem uniform_actual_mixing (n : ℕ) (hn : 2 ≤ n) {eps : ℝ} (heps : 0 < eps) :
    ∃ Q : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p → ∀ m : ℕ, 2 ≤ m →
      letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
      FatLadders.LocalMixing
        (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1) t : ℝ))
        (n+1) eps := by
  obtain ⟨Q₀,R,hcones⟩ := uniform_actual_proper_link_cones n (by omega)
  obtain ⟨Q₁,hspectral⟩ := exists_spectral_threshold (n+1-2) (lt_min heps zero_lt_one)
  refine ⟨max Q₀ Q₁,?_⟩
  intro p hp hq m hm
  exact actual_mixing_mono n (by omega) p m (min_le_left eps 1)
    (actual_mixing_level n hn p m hm (le_of_lt (lt_min heps zero_lt_one))
      (min_le_right eps 1) (hcones p hp ((le_max_left _ _).trans_lt hq) m hm)
      (hspectral p ((le_max_right _ _).trans_lt hq)))
end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Expansion
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.complexInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Local repairs, fat-ladder inequalities, and uniform raw cosystolic expansion.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
lemma linkLift_support (s : Finset V) (b : Finset V → k) :
    ∀ t, ¬ s ⊆ t → linkLift s b t = 0 := fun _ ht => ite_eq_right ht

omit [Fintype V] in
lemma delta_linkLift {s t : Finset V} (hst : s ⊆ t) (b : Finset V → k) :
    delta (linkLift s b) t = delta b (t \ s) := by
  unfold delta
  calc
    (∑ v ∈ t, linkLift s b (t.erase v)) = ∑ v ∈ t \ s, linkLift s b (t.erase v) := by
      symm
      apply Finset.sum_subset (Finset.sdiff_subset)
      intro v hvt hvs
      apply linkLift_support
      rw [Finset.subset_erase]
      simp only [hst,true_and]
      simpa [hvt] using hvs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvn := (Finset.mem_sdiff.mp hv).2
      rw [linkLift,ite_eq_left (Finset.subset_erase.mpr ⟨hst,hvn⟩),Finset.erase_sdiff_comm]

omit [Fintype V] in
lemma delta_linkRestrict (s : Finset V) (g : Finset V → k)
    (hg : ∀ t, ¬ s ⊆ t → g t = 0) {a : Finset V} (hdis : Disjoint s a) :
    delta (linkRestrict s g) a = delta g (s ∪ a) := by
  have hsd : (s ∪ a) \ s = a := Finset.union_sdiff_cancel_left hdis
  have hs : s ⊆ s ∪ a := Finset.subset_union_left
  have he : delta g (s ∪ a) = ∑ v ∈ a, g ((s ∪ a).erase v) := by
    unfold delta
    symm
    apply Finset.sum_subset (Finset.subset_union_right)
    intro v hv hva
    apply hg
    rw [Finset.subset_erase]
    simp only [hs,true_and]
    exact not_not.mpr ((Finset.mem_union.mp hv).resolve_right hva)
  rw [he]
  apply Finset.sum_congr rfl
  intro v hv
  have hn : v ∉ s := fun h => Finset.disjoint_left.mp hdis h hv
  change g (s ∪ a.erase v) = g ((s∪a).erase v)
  congr 1
  ext u
  simp only [Finset.mem_union,Finset.mem_erase]
  have hu : u ∈ s → u ≠ v := fun hu he => hn (he ▸ hu)
  tauto

lemma starNorm_linkNorm (w : Finset V → ℝ) (s : Finset V) (r : ℕ)
    (hr : s.card ≤ r) (g : Finset V → k) :
    starNorm w r s g = linkNorm w s (r-s.card) (linkRestrict s g) := by
  unfold starNorm starSum linkNorm
  rw [← Finset.sum_filter,← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ => s ∪ a)
  · intro a ha
    obtain ⟨ha,hd⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨mem_level.mpr ?_,Finset.subset_union_left⟩
    rw [Finset.card_union_of_disjoint hd,mem_level.mp ha]
    omega
  · intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have h := congrArg (fun t : Finset V => t \ s) he
    simpa only [Finset.union_sdiff_cancel_left ha',Finset.union_sdiff_cancel_left hb'] using h
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    refine ⟨t \ s,Finset.mem_filter.mpr ⟨mem_level.mpr ?_,(Finset.disjoint_left.mpr (fun v hv hvs => (Finset.mem_sdiff.mp hvs).2 hv))⟩,?_⟩
    · rw [Finset.card_sdiff_of_subset hst,mem_level.mp ht]
    · exact Finset.union_sdiff_of_subset hst
  · intro a ha
    rfl

lemma linkNorm_congr (w : Finset V → ℝ) (s : Finset V) (j : ℕ)
    (f g : Finset V → k) (he : ∀ a, a.card = j → Disjoint s a → f a = g a) :
    linkNorm w s j f = linkNorm w s j g := by
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs with h
  · rw [atom,atom,he a (mem_level.mp ha) h]
  · rfl

theorem linkCorrection_of_links {w : Finset V → ℝ} {r : ℕ} {C : ℝ}
    (hlocal : ∀ s : Finset V, s.Nonempty → s.card ≤ r →
      ∀ f : Finset V → k, ∃ b : Finset V → k,
        linkNorm w s (r-s.card) (f+delta b) ≤
          C*linkNorm w s (r-s.card+1) (delta f)) : LinkCorrection w r C := by
  intro s hs hr g hg
  obtain ⟨b,hb⟩ := hlocal s hs hr (linkRestrict s g)
  refine ⟨linkLift s b,linkLift_support s b,?_,?_⟩
  · intro he t ht
    by_cases hst : s ⊆ t
    · have hts : t = s := (Finset.eq_of_subset_of_card_le hst (by rw [mem_level.mp ht,he])).symm
      subst t
      rw [delta_linkLift (Finset.Subset.refl _),Finset.sdiff_self]
      simp [delta]
    · unfold delta
      apply Finset.sum_eq_zero
      intro v hv
      exact linkLift_support s b _ (fun h => hst (h.trans (Finset.erase_subset _ _)))
  · rw [starNorm_linkNorm w s r hr,starNorm_linkNorm w s (r+1) (by omega)]
    have hl : linkNorm w s (r-s.card) (linkRestrict s (g+delta (linkLift s b))) =
        linkNorm w s (r-s.card) (linkRestrict s g+delta b) := by
      apply linkNorm_congr
      intro a ha hd
      change g (s∪a)+delta (linkLift s b) (s∪a) = g (s∪a)+delta b a
      rw [delta_linkLift Finset.subset_union_left,Finset.union_sdiff_cancel_left hd]
    have hd : linkNorm w s (r+1-s.card) (linkRestrict s (delta g)) =
        linkNorm w s (r-s.card+1) (delta (linkRestrict s g)) := by
      have he : r+1-s.card = r-s.card+1 := by omega
      rw [he]
      apply linkNorm_congr
      intro a ha hda
      exact (delta_linkRestrict s g hg hda).symm
    rw [hl,hd]
    exact hb

end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.InfiniteChains
namespace FiniteWeights
open Cone Averaging
open scoped Pointwise
variable {V : Type} [DecidableEq V] [Fintype V]
attribute [local instance] Classical.propDecidable

lemma rawNorm_nonneg (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) (f : Finset V → k) : 0 ≤ rawNorm X N r f := by
  apply Finset.sum_nonneg
  intro s hs
  split_ifs <;> positivity

lemma rawNorm_weight (X : CoboundaryExpanders.InfiniteChains.Complex V) {N r : ℕ} (hr : r ≤ N) (hP : (level X N).Nonempty)
    (f : Finset V → k) :
    rawNorm X N r f = ((N.choose r:ℝ)*(level X N).card)*supportNorm (weight X N r) f := by
  have hd : (N.choose r:ℝ)*(level X N).card ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (Nat.choose_pos hr).ne')
      (by exact_mod_cast (Finset.card_pos.mpr hP).ne')
  unfold rawNorm
  calc
    _ = ∑ s ∈ level X r, ((N.choose r:ℝ)*(level X N).card)*
        (if f s = 0 then 0 else weight X N r s) := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hf : f s = 0
      · simp [hf]
      · simp only [hf,ne_eq,not_false_eq_true,ite_true,ite_false,weight,ite_eq_left hs]
        exact (mul_div_cancel₀ _ hd).symm
    _ = ∑ s, ((N.choose r:ℝ)*(level X N).card)*
        (if f s = 0 then 0 else weight X N r s) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s hs hn
      simp [weight,hn]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem raw_correction {G : Type} [Group G] [Fintype G] [MulAction G V]
    {X : CoboundaryExpanders.InfiniteChains.Complex V} {N n r R : ℕ} (hX : Invariant G X) (hP : Pure X N)
    (hTrans : ∀ a b : X.Face N, ∃ g : G, g • a.val = b.val)
    (H : BoundedCone X n R) (hr : r ≤ n) (hrN : r+1 ≤ N) (f : Finset V → k) :
    ∃ b : Finset V → k,
      rawNorm X N r (f+delta b) ≤ (R:ℝ)*(N.choose r)*rawNorm X N (r+1) (delta f) := by
  obtain ⟨b,hb⟩ := weighted_correction hX hP hTrans H hr hrN f
  refine ⟨b,?_⟩
  rw [rawNorm_weight X (by omega) hP.1,rawNorm_weight X hrN hP.1]
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (N.choose r:ℝ)*(level X N).card by positivity)
  change (N.choose r:ℝ) * (level X N).card * supportNorm (weight X N r)
    (fun s => f s + delta b s) ≤ _
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

lemma linkNorm_cofaces (X : CoboundaryExpanders.InfiniteChains.Complex V) {N : ℕ} {s : Finset V} (hs : s ∈ X.faces)
    (hN : s.card ≤ N) (j : ℕ) (f : Finset V → k) :
    FatLadders.linkNorm (fun t => (cofaces X N t:ℝ)) s j f =
      rawNorm (X.faceLink s hs) (N-s.card) j f := by
  have hl : FatLadders.level (V:=V) j = Finset.univ.filter (fun a : Finset V => a.card = j) := by
    ext a; simp [FatLadders.level]
  unfold FatLadders.linkNorm rawNorm level
  rw [hl]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hc : a.card = j
  · simp only [hc, and_true,ite_true]
    by_cases hd : Disjoint s a
    · rw [ite_eq_left hd]
      have he := cofaces_link X hs hN hd
      by_cases hf : a ∈ (X.faceLink s hs).faces
      · simp only [ite_eq_left hf,FatLadders.atom]
        rw [←he]
        by_cases hz : f a = 0 <;> simp [hz]
      · have hz := cofaces_zero_of_not_face (X.faceLink s hs) (N-s.card) hf
        simp only [FatLadders.atom]
        rw [←he,hz]
        simp [hf]
    · have hf : a ∉ (X.faceLink s hs).faces := fun h => hd h.1
      simp [hd,hf]
  · simp [hc]

end FiniteWeights
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces

section
open InfiniteChains
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

omit [DecidableEq I] in
lemma IsFace.type_injective {s : Finset (Vertex H)} (hs : IsFace H s) :
    Set.InjOn Sigma.fst (s : Set (Vertex H)) := by
  obtain ⟨g,A,rfl⟩ := hs
  intro x hx y hy hxy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
  change i=j at hxy
  subst j
  rfl

omit [DecidableEq I] in
lemma faceStabilizer_fixes (s : Finset (Vertex H)) (g : faceStabilizer H s) :
    (g.val:G) • s = s := g.property

lemma facesLinkInvariant {s : Finset (Vertex H)} (hs : IsFace H s)
    (g : faceStabilizer H s) {a : Finset (Vertex H)}
    (ha : a ∈ ((complex H).faceLink s hs).faces) :
    g • a ∈ ((complex H).faceLink s hs).faces := by
  change Disjoint s ((g.val:G) • a) ∧ IsFace H (s ∪ (g.val:G) • a)
  have hg := faceStabilizer_fixes H s g
  constructor
  · have hd : Disjoint ((g.val:G) • s) ((g.val:G) • a) := by
      simp only [Finset.smul_finset_def]
      exact (Finset.disjoint_image (f:=fun v : Vertex H => (g.val:G) • v)
        (MulAction.injective (β:=Vertex H) (g.val:G))).mpr ha.1
    simpa only [hg] using hd
  · have hh := ha.2.smul H (g.val:G)
    rw [Finset.smul_finset_union,hg] at hh
    exact hh

lemma facesLinkTransitive [Fintype I] {s : Finset (Vertex H)} (hs : IsFace H s)
    {a b : Finset (Vertex H)} (ha : a ∈ ((complex H).faceLink s hs).faces)
    (hb : b ∈ ((complex H).faceLink s hs).faces)
    (hsc : s.card ≤ Fintype.card I)
    (hac : a.card = Fintype.card I-s.card)
    (hbc : b.card = Fintype.card I-s.card) :
    ∃ g : faceStabilizer H s, g • a = b := by
  have hsa : (s∪a).card = Fintype.card I := by
    rw [Finset.card_union_of_disjoint ha.1,hac,Nat.add_sub_of_le hsc]
  have hsb : (s∪b).card = Fintype.card I := by
    rw [Finset.card_union_of_disjoint hb.1,hbc,Nat.add_sub_of_le hsc]
  obtain ⟨g,hg⟩ := chamber_transitive H ha.2 hb.2 hsa hsb
  have hpoint (v : Vertex H) (hv : v ∈ s) : g • v = v := by
    apply hb.2.type_injective H
    · rw [←hg]
      exact Finset.mem_smul_finset.mpr ⟨v,Finset.mem_union_left a hv,rfl⟩
    · exact Finset.mem_union_left b hv
    · rfl
  have hfix : g • s = s := by
    change s.image (fun v => g • v) = s
    calc
      _ = s.image id := Finset.image_congr hpoint
      _ = s := Finset.image_id
  have hdis : Disjoint s (g • a) := by
    rw [←hfix]
    simp only [Finset.smul_finset_def]
    exact (Finset.disjoint_image (f:=fun v : Vertex H => g • v)
      (MulAction.injective (β:=Vertex H) g)).mpr ha.1
  refine ⟨⟨g,hfix⟩,?_⟩
  change g • a = b
  rw [Finset.smul_finset_union,hfix] at hg
  have he := congrArg (fun t : Finset (Vertex H) => t \ s) hg
  simpa only [Finset.union_sdiff_cancel_left hdis,Finset.union_sdiff_cancel_left hb.1] using he

end

open InfiniteChains FiniteWeights Cone
open scoped Pointwise
variable {G I : Type} [Group G] [Fintype G] [DecidableEq I] [Fintype I] (H : I → Subgroup G)
omit [Fintype G] [DecidableEq I] [Fintype I] in
lemma delta_agrees (g : Finset (Vertex H) → k) : Cone.delta g = FatLadders.delta g := by
  funext s
  exact Cone.delta_eq_sum g s

theorem linkCorrection_of_cones {R r : ℕ}
    (hR : ProperLinkCones (complex H) (Fintype.card I) R) (hr : r < Fintype.card I) :
    FatLadders.LinkCorrection (fun t => (cofaces (complex H) (Fintype.card I) t : ℝ)) r
      ((R:ℝ)*2^(Fintype.card I)) := by
  apply FatLadders.linkCorrection_of_links
  intro s hne hsr f
  by_cases hs : s ∈ (complex H).faces
  · let : Fintype (faceStabilizer H s) := Fintype.ofFinite _
    have hsc : s.card ≤ Fintype.card I := by omega
    have hlocal := hR s hne hs (by omega)
    have hp := pure_link (finite_pure H) hs
    have hi : Invariant (faceStabilizer H s) ((complex H).faceLink s hs) :=
      fun g a ha => facesLinkInvariant H hs g ha
    have ht : ∀ a b : ((complex H).faceLink s hs).Face (Fintype.card I-s.card),
        ∃ g : faceStabilizer H s, g • a.val = b.val := by
      intro a b
      exact facesLinkTransitive H hs a.property.1 b.property.1 hsc a.property.2 b.property.2
    obtain ⟨b,hb⟩ := raw_correction hi hp ht hlocal.some
      (show r-s.card ≤ Fintype.card I-s.card-1 by omega)
      (show r-s.card+1 ≤ Fintype.card I-s.card by omega) f
    refine ⟨b,?_⟩
    rw [linkNorm_cofaces (complex H) hs hsc,linkNorm_cofaces (complex H) hs hsc]
    rw [delta_agrees H b,delta_agrees H f] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (rawNorm_nonneg _ _ _ _)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg R)
    have hc := Nat.choose_le_two_pow (Fintype.card I-s.card) (r-s.card)
    have he : 2^(Fintype.card I-s.card) ≤ 2^(Fintype.card I) :=
      Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    exact_mod_cast hc.trans he
  · have hz (a : Finset (Vertex H)) : cofaces (complex H) (Fintype.card I) (s∪a) = 0 :=
      cofaces_zero_of_not_face _ _ (fun ha => hs ((complex H).downward ha Finset.subset_union_left))
    refine ⟨0,?_⟩
    simp [FatLadders.linkNorm,FatLadders.atom,hz]

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open InfiniteChains FiniteWeights TypedCosetFaces

theorem uniform_actual_linkCorrection (n : ℕ) (hn : 1 ≤ n) :
    ∃ Q C : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p →
      ∀ m : ℕ, 2 ≤ m →
      letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
      ∀ r : ℕ, r < n+1 →
      FatLadders.LinkCorrection
        (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n hn m)) (n+1) t : ℝ)) r C := by
  obtain ⟨Q,R,h⟩ := uniform_actual_proper_link_cones n hn
  refine ⟨Q,R*2^(n+1),?_⟩
  intro p hp hq m hm
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  intro r hr
  have hh := linkCorrection_of_cones (reducedLocalGroup p n hn m)
    (by simpa only [Fintype.card_fin] using h p hp hq m hm)
    (by simpa only [Fintype.card_fin] using hr)
  simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
lemma delta_insert (f : Finset V → k) (v : V) (s : Finset V) (hv : v ∉ s) :
    delta f (insert v s) = f s + delta (fun t => f (insert v t)) s := by
  unfold delta
  rw [Finset.sum_insert hv,Finset.erase_insert hv]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.erase_insert_of_ne (by intro e; subst v; exact hv hx)]

omit [Fintype V] in
@[simp] theorem delta_delta (f : Finset V → k) : delta (delta f) = 0 := by
  funext s
  change delta (delta f) s = 0
  induction s using Finset.induction_on generalizing f with
  | empty => simp [delta]
  | @insert v s hv ih =>
      rw [delta_insert _ v s hv]
      have he : delta (fun t => delta f (insert v t)) s =
          delta f s + delta (delta (fun t => f (insert v t))) s := by
        unfold delta
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        exact delta_insert f v (s.erase x) (fun h => hv (Finset.mem_of_mem_erase h))
      rw [he,ih]
      simp [CharTwo.add_self_eq_zero]

omit [Fintype V] in
lemma delta_support {s : Finset V} {f : Finset V → k}
    (hf : ∀ t, ¬s ⊆ t → f t = 0) : ∀ t, ¬s ⊆ t → delta f t = 0 := by
  intro t ht
  apply Finset.sum_eq_zero
  intro x hx
  exact hf _ (fun h => ht (h.trans (Finset.erase_subset _ _)))

omit [DecidableEq V] in
lemma WeightedEq.atom_eq {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) {s} (hs : s ∈ level r) : atom w f s = atom w g s := by
  by_cases hz : w s = 0
  · simp [atom,hz]
  · rw [atom,atom,h s hs hz]

omit [DecidableEq V] in
lemma WeightedEq.norm_eq {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) : norm w r f = norm w r g :=
  Finset.sum_congr rfl (fun _ hs => h.atom_eq hs)

lemma WeightedEq.starNorm_eq {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) (s) : starNorm w r s f = starNorm w r s g := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h.atom_eq ht]

omit [DecidableEq V] in
lemma WeightedEq.add_right {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) (b : Finset V → k) : WeightedEq w r (f+b) (g+b) := by
  intro s hs hw
  simp only [Pi.add_apply,h s hs hw]

lemma WeightedEq.delta_eq {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    {f g : Finset V → k} (h : WeightedEq w r f g) : WeightedEq w (r+1) (delta f) (delta g) := by
  intro s hs hws
  apply Finset.sum_congr rfl
  intro x hx
  have he : s.erase x ∈ level r := by
    apply mem_level.mpr
    rw [Finset.card_erase_of_mem hx,mem_level.mp hs]
    omega
  apply h _ he
  intro hz
  exact hws (hw.weight_eq_zero_of_base (Finset.erase_subset x s) hz)

lemma WeightedEq.nearMinimal {w : Finset V → ℝ} {r : ℕ} {f g : Finset V → k}
    (h : WeightedEq w r f g) {ε : ℝ} (hf : NearMinimal w r ε f) : NearMinimal w r ε g := by
  intro s hs hsr b hb
  have hh := hf s hs hsr b hb
  rwa [h.starNorm_eq s,(h.add_right (delta b)).starNorm_eq s] at hh

lemma fatFamily_top_eq {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (N r : ℕ) (θ : ℕ → ℝ) (f : Finset V → k) :
    WeightedEq w r f (indicator (fatFamily w N r θ f)) := by
  intro s hs hws
  have hpos := lt_of_le_of_ne (hw s) (Ne.symm hws)
  have hc := mem_level.mp hs
  simp only [indicator,fatFamily,hc,le_refl,true_and,Nat.sub_self,fatAt,hpos,and_true]
  have htwo : ∀ x : k, x = 0 ∨ x = 1 := by decide
  rcases htwo (f s) with hf | hf <;> simp [hf]

theorem small_cochain_expansion {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) (hw0 : w ∅ = 1) {η lam ε C : ℝ}
    (hη : 0 < η) (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hC : 0 < C)
    (hεsmall : ε*(2:ℝ)^r ≤ 1/2)
    (hηsmall : C*(2:ℝ)^(r+1)*((2:ℝ)^N*(N:ℝ)^2*(r:ℝ)*(2*η)) ≤ 1/4)
    (hbudget : ∀ a ≤ r, lam*fatBudget N η a ≤ η)
    (hmix : LocalMixing w N lam) (hcor : LinkCorrection w r C)
    (f : Finset V → k) (hmin : NearMinimal w r ε f)
    (hsmall : norm w r f < 1/fatBudget N η r) :
    (1/4:ℝ)*norm w r f ≤ C*(2:ℝ)^(r+1)*norm w (r+1) (delta f) := by
  let F := fatFamily w N r (fatThreshold N r η) f
  have hEq := fatFamily_top_eq hw.nonneg N r (fatThreshold N r η) f
  have hF : ¬ F ∅ := fat_empty_false hw hN hrN hw0 hη f hsmall
  have hbad : C*(2:ℝ)^(r+1)*norm w (r+1) (indicator (fun T => ¬NoBad F T)) ≤
      (1/4:ℝ)*norm w r (indicator F) := by
    have hd := fat_degeneracy_bound hw hN hrN hη hlam hbudget hmix f (r+1)
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ C*(2:ℝ)^(r+1) by positivity)
    have hh' := mul_le_mul_of_nonneg_right hηsmall (norm_nonneg hw.nonneg r f)
    rw [hEq.norm_eq] at hh'
    exact hh.trans (by simpa only [← mul_assoc,hEq.norm_eq] using hh')
  have hh := small_set_expansion hw.nonneg hF hε hC hεsmall (hEq.nearMinimal hmin) hcor hbad
  rwa [← hEq.norm_eq,← (hEq.delta_eq hw).norm_eq] at hh

end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.LocalRepair

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem repair [Fintype A] (na : Size A) (nb : Size B) (δ : A →+ B)
    (P : B → Prop) {C : ℝ} (_ : 0 ≤ C)
    (hstep : ∀ a : A, ¬ P (δ a) → ∃ u : A,
      nb (δ (a+u)) < nb (δ a) ∧
      na u ≤ C * (nb (δ a) - nb (δ (a+u)))) (f : A) :
    ∃ h : A, P (δ (f+h)) ∧ nb (δ (f+h)) ≤ nb (δ f) ∧
      na h ≤ C * (nb (δ f) - nb (δ (f+h))) := by
  classical
  let S : Finset A := Finset.univ.filter (fun h =>
    na h ≤ C * (nb (δ f) - nb (δ (f+h))))
  have hz : (0 : A) ∈ S := by simp [S,na.zero]
  obtain ⟨h,hh,hmin⟩ := S.exists_min_image (fun h => nb (δ (f+h))) ⟨0,hz⟩
  have hbound : na h ≤ C * (nb (δ f) - nb (δ (f+h))) := (Finset.mem_filter.mp hh).2
  refine ⟨h,?_,by simpa only [add_zero] using hmin 0 hz,hbound⟩
  by_contra hp
  obtain ⟨u,hu,hcost⟩ := hstep (f+h) hp
  have hmem : h+u ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    calc
      na (h+u) ≤ na h + na u := na.triangle h u
      _ ≤ C * (nb (δ f) - nb (δ (f+h))) +
          C * (nb (δ (f+h)) - nb (δ ((f+h)+u))) := add_le_add hbound hcost
      _ = C * (nb (δ f) - nb (δ (f+(h+u)))) := by rw [add_assoc]; ring
  have hcontra := hmin (h+u) hmem
  rw [← add_assoc] at hcontra
  exact (not_lt_of_ge hcontra) hu

end CoboundaryExpanders.LocalRepair

namespace CoboundaryExpanders.FatLadders

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma support_starNorm {w : Finset V → ℝ} {r : ℕ} {s : Finset V} {f : Finset V → k}
    (hf : ∀ t, ¬s ⊆ t → f t = 0) : starNorm w r s f = norm w r f := by
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : s ⊆ t
  · exact ite_eq_left hs
  · simp [hs,atom,hf t hs]

lemma local_global_difference (w : Finset V → ℝ) (r : ℕ) (s : Finset V)
    (f g : Finset V → k) (hg : ∀ t, ¬s ⊆ t → g t = 0) :
    norm w r f - norm w r (f+g) = starNorm w r s f - starNorm w r s (f+g) := by
  unfold norm starNorm starSum
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : s ⊆ t
  · simp [hs]
  · simp [hs,atom,hg t hs]

theorem nearMinimal_repair_step {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {r : ℕ} {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hcor : LinkCorrection w (r-1) C) (f : Finset V → k)
    (hmin : ¬NearMinimal w r ε f) :
    ∃ u : Finset V → k, norm w r (f+delta u) < norm w r f ∧
      norm w (r-1) u ≤ (2*C/ε)*(norm w r f-norm w r (f+delta u)) := by
  unfold NearMinimal at hmin
  push Not at hmin
  obtain ⟨s,hs,hsr,b,hb,hdec⟩ := hmin
  obtain ⟨c,hc,htop,hcost⟩ := hcor s hs (by omega) b hb
  let u := b+delta c
  have hdu : delta u = delta b := by simp [u]
  have hu : ∀ t, ¬s ⊆ t → u t = 0 := by
    intro t ht
    simp [u,hb t ht,delta_support hc t ht]
  have hd : ∀ t, ¬s ⊆ t → delta b t = 0 := delta_support hb
  have hdiff := local_global_difference w r s f (delta b) hd
  have hm := starNorm_nonneg hw r s f
  have hm' := starNorm_nonneg hw r s (f+delta b)
  have hpositive : 0 < starNorm w r s f := by nlinarith
  have hstrict : norm w r (f+delta b) < norm w r f := by nlinarith
  have hid : delta b = f+(f+delta b) := by
    funext t
    simp only [Pi.add_apply,← add_assoc,CharTwo.add_self_eq_zero,zero_add]
  have htriangle : starNorm w r s (delta b) ≤
      starNorm w r s f+starNorm w r s (f+delta b) := by
    conv_lhs => rw [hid]
    exact starNorm_add_le hw r s f (f+delta b)
  have hrone : r-1+1 = r := by have := hs.card_pos; omega
  rw [hrone,support_starNorm hu] at hcost
  refine ⟨u,by rwa [hdu],?_⟩
  rw [hdu]
  calc
    norm w (r-1) u ≤ C*starNorm w r s (delta b) := hcost
    _ ≤ C*(starNorm w r s f+starNorm w r s (f+delta b)) :=
      mul_le_mul_of_nonneg_left htriangle hC
    _ ≤ 2*C*starNorm w r s f := by nlinarith
    _ ≤ (2*C/ε)*(norm w r f-norm w r (f+delta b)) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hε).mpr
      have hsmall : ε*starNorm w r s f ≤ norm w r f-norm w r (f+delta b) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2*C by positivity)]

theorem repair_coboundary {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {r : ℕ} {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hcor : LinkCorrection w (r-1) C) (f : Finset V → k) :
    ∃ h : Finset V → k, NearMinimal w r ε (delta (f+h)) ∧
      norm w r (delta (f+h)) ≤ norm w r (delta f) ∧
      norm w (r-1) h ≤ (2*C/ε)*(norm w r (delta f)-norm w r (delta (f+h))) := by
  apply LocalRepair.repair (normSize w hw (r-1)) (normSize w hw r) deltaHom
    (NearMinimal w r ε) (div_nonneg (by positivity) hε.le) _ f
  intro a ha
  obtain ⟨u,hdec,hcost⟩ := nearMinimal_repair_step hw hε hC hcor (delta a) ha
  refine ⟨u,?_,?_⟩
  · change norm w r (delta (a+u)) < norm w r (delta a)
    simpa only [delta_add] using hdec
  · change norm w (r-1) u ≤ (2*C/ε)*(norm w r (delta a)-norm w r (delta (a+u)))
    simpa only [delta_add] using hcost

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma norm_le_choose {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (hw0 : w ∅ = 1) (r : ℕ) (f : Finset V → k) :
    norm w r f ≤ (Nat.choose N r : ℝ) := by
  calc
    norm w r f ≤ ∑ t ∈ level r, w t := Finset.sum_le_sum (fun t _ => atom_le_weight hw.nonneg f t)
    _ = starSum r ∅ w := by simp [starSum]
    _ = _ := by rw [hw.balance ∅ r (by simp)]; simp [hw0]

theorem cosystolic_from_local {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) (hw0 : w ∅ = 1) {η lam ε C : ℝ}
    (hη : 0 < η) (hlam : 0 ≤ lam) (hε : 0 < ε) (hC : 0 < C)
    (hεsmall : ε*(2:ℝ)^r ≤ 1/2)
    (hηsmall : C*(2:ℝ)^(r+1)*((2:ℝ)^N*(N:ℝ)^2*(r:ℝ)*(2*η)) ≤ 1/4)
    (hbudget : ∀ a ≤ r, lam*fatBudget N η a ≤ η)
    (hmix : LocalMixing w N lam) (hcor : LinkCorrection w r C)
    (hcor' : LinkCorrection w (r-1) C) (f : Finset V → k) :
    ∃ h : Finset V → k, norm w r (delta (f+h)) = 0 ∧
      norm w (r-1) h ≤
        (1+2*C/ε+(Nat.choose N (r-1):ℝ)*fatBudget N η r)*norm w r (delta f) := by
  let μ := 1/fatBudget N η r
  have hμ : 0 < μ := one_div_pos.mpr (fatBudget_pos hN hη r)
  have hC0 : 0 ≤ 2*C/ε := div_nonneg (by positivity) hε.le
  have hB0 : 0 ≤ (Nat.choose N (r-1):ℝ)*fatBudget N η r :=
    mul_nonneg (Nat.cast_nonneg _) (fatBudget_pos hN hη r).le
  by_cases hf : norm w r (delta f) < μ
  · obtain ⟨h,hmin,hdecrease,hcost⟩ := repair_coboundary hw.nonneg hε hC.le hcor' f
    have hs := small_cochain_expansion hw hN hrN hw0 hη hlam hε.le hC hεsmall hηsmall
      hbudget hmix hcor (delta (f+h)) hmin (hdecrease.trans_lt hf)
    rw [delta_delta,norm_zero,mul_zero] at hs
    have hz : norm w r (delta (f+h)) = 0 := by
      have hn := norm_nonneg hw.nonneg r (delta (f+h))
      linarith
    refine ⟨h,hz,?_⟩
    rw [hz,sub_zero] at hcost
    apply hcost.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg hw.nonneg r (delta f))
    linarith
  · refine ⟨-f,by simp,?_⟩
    have hbig : μ ≤ norm w r (delta f) := le_of_not_gt hf
    have hbound := mul_le_mul_of_nonneg_left hbig hB0
    have hident : (Nat.choose N (r-1):ℝ)*fatBudget N η r*μ = (Nat.choose N (r-1):ℝ) := by
      dsimp [μ]
      field_simp [ne_of_gt (fatBudget_pos hN hη r)]
    rw [hident] at hbound
    calc
      norm w (r-1) (-f) ≤ (Nat.choose N (r-1):ℝ) := norm_le_choose hw hw0 _ _
      _ ≤ (Nat.choose N (r-1):ℝ)*fatBudget N η r*norm w r (delta f) := hbound
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg hw.nonneg r (delta f))
        linarith

theorem uniform_cosystolic_from_local (N r : ℕ) (hN : 0 < N) (hrN : r ≤ N)
    (C : ℝ) (hC : 0 < C) :
    ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (w : Finset V → ℝ), Balanced w N → w ∅ = 1 →
      LocalMixing w N lam → LinkCorrection w r C → LinkCorrection w (r-1) C →
      ∀ f : Finset V → k, ∃ h : Finset V → k,
        norm w r (delta (f+h)) = 0 ∧ norm w (r-1) h ≤ K*norm w r (delta f) := by
  let A : ℝ := C*(2:ℝ)^(r+1)*(2:ℝ)^N*(N:ℝ)^2*(r:ℝ)*2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let η : ℝ := 1/(4*(A+1))
  have hden : 0 < 4*(A+1) := by linarith
  have hη : 0 < η := one_div_pos.mpr hden
  have hηsmall : C*(2:ℝ)^(r+1)*((2:ℝ)^N*(N:ℝ)^2*(r:ℝ)*(2*η)) ≤ 1/4 := by
    have hh : A*η ≤ 1/4 := by
      dsimp [η]
      rw [mul_one_div]
      apply (div_le_iff₀ hden).mpr
      linarith
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [A]
    ring
  let ε : ℝ := 1/(2*(2:ℝ)^r)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεsmall : ε*(2:ℝ)^r ≤ 1/2 := by dsimp [ε]; field_simp; norm_num
  obtain ⟨lam,hlam,hbudget⟩ := exists_mixing_tolerance N r hN hη
  let K : ℝ := 1+2*C/ε+(Nat.choose N (r-1):ℝ)*fatBudget N η r
  have hK : 0 < K := by
    have hb := fatBudget_pos hN hη r
    dsimp [K]
    positivity
  refine ⟨lam,K,hlam,hK,?_⟩
  intro V _ _ w hw hw0 hmix hcor hcor' f
  exact cosystolic_from_local hw hN hrN hw0 hη hlam.le hε hC hεsmall hηsmall hbudget
    hmix hcor hcor' f

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] in
lemma atom_scale (w : Finset V → ℝ) (a : ℝ) (f : Finset V → k) (s) :
    atom (fun t => a*w t) f s = a*atom w f s := by
  unfold atom
  split_ifs <;> simp
omit [DecidableEq V] in
lemma norm_scale (w : Finset V → ℝ) (a : ℝ) (r) (f : Finset V → k) :
    norm (fun t => a*w t) r f = a*norm w r f := by
  simp only [norm,atom_scale,Finset.mul_sum]
lemma starSum_scale (w : Finset V → ℝ) (a : ℝ) (r s) :
    starSum r s (fun t => a*w t) = a*starSum r s w := by
  simp only [starSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp
lemma starNorm_scale (w : Finset V → ℝ) (a : ℝ) (r s) (f : Finset V → k) :
    starNorm (fun t => a*w t) r s f = a*starNorm w r s f := by
  unfold starNorm starSum
  simp only [atom_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp
lemma collisionMass_scale (w : Finset V → ℝ) (a : ℝ) (F : Finset V → Prop) (s) :
    collisionMass (fun t => a*w t) F s = a*collisionMass w F s := by
  simp only [collisionMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp
lemma Balanced.scale {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {a : ℝ} (ha : 0 ≤ a) : Balanced (fun t => a*w t) N := by
  refine ⟨fun s => mul_nonneg ha (hw.nonneg s),fun s hs => by rw [hw.vanish s hs,mul_zero],?_⟩
  intro s r hr
  rw [starSum_scale,hw.balance s r hr]
  ring
lemma LinkCorrection.scale {w : Finset V → ℝ} {r : ℕ} {C a : ℝ}
    (hc : LinkCorrection w r C) (ha : 0 ≤ a) : LinkCorrection (fun t => a*w t) r C := by
  intro s hs hsr g hg
  obtain ⟨b,hb,he,hbound⟩ := hc s hs hsr g hg
  refine ⟨b,hb,he,?_⟩
  rw [starNorm_scale,starNorm_scale,mul_left_comm C a]
  exact mul_le_mul_of_nonneg_left hbound ha
lemma LinkCorrection.mono {w : Finset V → ℝ} (hw : ∀s,0≤w s)
    {r : ℕ} {C D : ℝ} (hc : LinkCorrection w r C) (hCD : C ≤ D) : LinkCorrection w r D := by
  intro s hs hsr g hg
  obtain ⟨b,hb,he,hbound⟩ := hc s hs hsr g hg
  exact ⟨b,hb,he,hbound.trans (mul_le_mul_of_nonneg_right hCD (starNorm_nonneg hw _ _ _))⟩
lemma LocalMixing.scale {w : Finset V → ℝ} {N : ℕ} {lam a : ℝ}
    (hm : LocalMixing w N lam) (ha : 0 < a) : LocalMixing (fun t => a*w t) N lam := by
  intro F s hs t ht hbound
  rw [starNorm_scale] at hbound
  have hb : starNorm w (s.card+1) s (indicator F) ≤ t*(N-s.card:ℕ)*w s := by
    apply (mul_le_mul_iff_right₀ ha).mp
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound
  have h := mul_le_mul_of_nonneg_left (hm F s hs t ht hb) ha.le
  rw [collisionMass_scale,starNorm_scale]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h
lemma LocalMixing.mono {w : Finset V → ℝ} (hw : ∀s,0≤w s)
    {N : ℕ} {lam mu : ℝ} (hm : LocalMixing w N lam) (hlm : lam ≤ mu) :
    LocalMixing w N mu := by
  intro F s hs t ht hbound
  apply (hm F s hs t ht hbound).trans
  apply mul_le_mul_of_nonneg_right _ (starNorm_nonneg hw _ _ _)
  exact mul_le_mul_of_nonneg_right (add_le_add_right hlm t) (Nat.cast_nonneg N)

end

theorem uniform_all_cosystolic_from_local (N : ℕ) (hN : 0 < N) (C : ℝ) (hC : 0 < C) :
    ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (w : Finset V → ℝ), Balanced w N → w ∅ = 1 →
      LocalMixing w N lam → (∀ r < N, LinkCorrection w r C) →
      ∀ r < N, ∀ f : Finset V → k, ∃ h : Finset V → k,
        norm w r (delta (f+h)) = 0 ∧ norm w (r-1) h ≤ K*norm w r (delta f) := by
  have aux : ∀ m ≤ N, ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (w : Finset V → ℝ), Balanced w N → w ∅ = 1 →
      LocalMixing w N lam → (∀ r < N, LinkCorrection w r C) →
      ∀ r < m, ∀ f : Finset V → k, ∃ h : Finset V → k,
        norm w r (delta (f+h)) = 0 ∧ norm w (r-1) h ≤ K*norm w r (delta f) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1,1,by norm_num,by norm_num,?_⟩
      intro V _ _ w hw hw0 hm hc r hr
      omega
    | succ m ih =>
      intro hmN
      obtain ⟨l₀,K₀,hl₀,hK₀,h₀⟩ := ih (by omega)
      obtain ⟨l₁,K₁,hl₁,hK₁,h₁⟩ := uniform_cosystolic_from_local N m hN (by omega) C hC
      refine ⟨min l₀ l₁,max K₀ K₁,lt_min hl₀ hl₁,hK₀.trans_le (le_max_left _ _),?_⟩
      intro V _ _ w hw hw0 hm hc r hr f
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · obtain ⟨h,hz,hb⟩ := h₀ V w hw hw0 (hm.mono hw.nonneg (min_le_left _ _)) hc r hr f
        exact ⟨h,hz,hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg hw.nonneg r _))⟩
      · obtain ⟨h,hz,hb⟩ := h₁ V w hw hw0 (hm.mono hw.nonneg (min_le_right _ _))
          (hc r (by omega)) (hc (r-1) (by omega)) f
        exact ⟨h,hz,hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg hw.nonneg r _))⟩
  exact aux N le_rfl

theorem uniform_raw_cosystolic_from_local (N : ℕ) (hN : 0 < N) (C : ℝ) (hC : 0 < C) :
    ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (w : Finset V → ℝ), Balanced w N → 0 < w ∅ →
      LocalMixing w N lam → (∀ r < N, LinkCorrection w r C) →
      ∀ r < N, ∀ f : Finset V → k, ∃ h : Finset V → k,
        norm w r (delta (f+h)) = 0 ∧ norm w (r-1) h ≤ K*norm w r (delta f) := by
  obtain ⟨lam,K,hlam,hK,hh⟩ := uniform_all_cosystolic_from_local N hN C hC
  refine ⟨lam,K,hlam,hK,?_⟩
  intro V _ _ w hw hw0 hmix hcor r hr f
  have ha : 0 < (w ∅)⁻¹ := inv_pos.mpr hw0
  have hn : (w ∅)⁻¹*w ∅ = 1 := inv_mul_cancel₀ hw0.ne'
  obtain ⟨h,hz,hb⟩ := hh V (fun s => (w ∅)⁻¹*w s) (hw.scale ha.le) hn
    (hmix.scale ha) (fun r hr => (hcor r hr).scale ha.le) r hr f
  simp only [norm_scale] at hz hb
  refine ⟨h,(mul_eq_zero.mp hz).resolve_left ha.ne',?_⟩
  apply (mul_le_mul_iff_right₀ ha).mp
  simpa only [mul_comm,mul_left_comm,mul_assoc] using hb
end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.Construction
open InfiniteChains FiniteWeights TypedCosetFaces

theorem uniform_actual_raw_cosystolic (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p →
      ∀ m : ℕ, 2 ≤ m →
      letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
      let w := fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1) t : ℝ)
      ∀ r : ℕ, r < n+1 → ∀ f : Finset (Vertex (reducedLocalGroup p n (by omega) m)) → ZMod 2,
        ∃ h, FatLadders.norm w r (FatLadders.delta (f+h)) = 0 ∧
          FatLadders.norm w (r-1) h ≤ K * FatLadders.norm w r (FatLadders.delta f) := by
  obtain ⟨Q₀,C,hC⟩ := uniform_actual_linkCorrection n (by omega)
  have hCp : 0 < (C:ℝ)+1 := by positivity
  obtain ⟨lam,K,hlam,hK,hraw⟩ := FatLadders.uniform_raw_cosystolic_from_local (n+1) (by omega) ((C:ℝ)+1) hCp
  obtain ⟨Q₁,hmix⟩ := uniform_actual_mixing n hn hlam
  refine ⟨max Q₀ Q₁,K,hK,?_⟩
  intro p hp hq m hm
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  dsimp only
  have hP := finite_pure (reducedLocalGroup p n (by omega) m)
  rw [Fintype.card_fin] at hP
  apply hraw _ _ (cofaces_balanced _ (n+1))
  · exact_mod_cast (cofaces_pos_iff hP ∅).mpr (TypedCosetFaces.complex _).empty_mem
  · exact hmix p hp ((le_max_right _ _).trans_lt hq) m hm
  · intro r hr
    exact (hC p hp ((le_max_left _ _).trans_lt hq) m hm r hr).mono
      (fun s => Nat.cast_nonneg _) (by linarith)
end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite labeled coset complexes, purity, growth, incidence bounds, and weighted expansion reduction.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.CosetConstruction

section

open CoboundaryExpanders.Complex

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem vertex_type_eq {H : Fin (n + 1) → Subgroup G} {g h : G} {i j : Fin (n + 1)}
    (heq : vertex H g i = vertex H h j) : i = j :=
  congrArg Sigma.fst ((labelEquiv H).injective heq)

theorem vertex_injective (H : Fin (n + 1) → Subgroup G) (g : G) :
    Function.Injective (vertex H g) := fun _ _ heq => vertex_type_eq heq

theorem vertex_eq_iff (H : Fin (n + 1) → Subgroup G) (g h : G) (i : Fin (n + 1)) :
    vertex H g i = vertex H h i ↔ g⁻¹ * h ∈ H i := by
  change labelEquiv H ⟨i, (g : G ⧸ H i)⟩ = labelEquiv H ⟨i, (h : G ⧸ H i)⟩ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  simpa using (QuotientGroup.eq (s := H i) (a := g) (b := h))

@[simp] theorem card_chamber (H : Fin (n + 1) → Subgroup G) (g : G) :
    (chamber H g).card = n + 1 := by
  rw [chamber, Finset.card_image_of_injective _ (vertex_injective H g)]
  simp

@[simp] theorem chamber_mem_facesOf (H : Fin (n + 1) → Subgroup G) (g : G) :
    chamber H g ∈ (complex H).facesOf n := by
  exact (mem_facesOf _ _ _).mpr ⟨mem_faces.mpr ⟨g, Finset.Subset.refl _⟩,
    card_chamber H g⟩

theorem pure (H : Fin (n + 1) → Subgroup G) : (complex H).Pure n := by
  refine ⟨⟨chamber H 1, chamber_mem_facesOf H 1⟩, ?_⟩
  intro σ hσ
  obtain ⟨g, hg⟩ := mem_faces.mp hσ
  exact ⟨chamber H g, chamber_mem_facesOf H g, hg⟩

theorem card_incidentInChamber (H : Fin (n + 1) → Subgroup G) (g : G)
    (v : Fin (Fintype.card (Vertex H))) (d : ℕ) (hv : v ∈ chamber H g) :
    (incidentInChamber H g v d).card = Nat.choose n d := by
  have h := Finset.card_filter_powersetCard_subset {v} (chamber H g) (d + 1)
    (Finset.singleton_subset_iff.mpr hv) (by simp)
  simpa [incidentInChamber] using h

attribute [local instance] OAI.CoboundaryExpanders.CosetConstruction.subgroupFintype
theorem incident_faces_subset (H : Fin (n + 1) → Subgroup G) (g : G)
    (i : Fin (n + 1)) (d : ℕ) :
    ((complex H).facesOf d).filter (vertex H g i ∈ ·) ⊆
      Finset.univ.biUnion (fun h : H i =>
        incidentInChamber H (g * h) (vertex H g i) d) := by
  intro σ hσ
  obtain ⟨hσ, hv⟩ := Finset.mem_filter.mp hσ
  obtain ⟨hface, hcard⟩ := (mem_facesOf _ _ _).mp hσ
  obtain ⟨k, hk⟩ := mem_faces.mp hface
  obtain ⟨j, hj⟩ := mem_chamber.mp (hk hv)
  have hji : j = i := vertex_type_eq hj
  subst j
  have hmem : g⁻¹ * k ∈ H i := (vertex_eq_iff H g k i).mp hj.symm
  refine Finset.mem_biUnion.mpr ⟨⟨g⁻¹ * k, hmem⟩, Finset.mem_univ _, ?_⟩
  apply mem_incidentInChamber.mpr
  simpa only [mul_inv_cancel_left] using And.intro hk (And.intro hcard hv)

theorem topDegree_le (H : Fin (n + 1) → Subgroup G) (g : G)
    (i : Fin (n + 1)) (d : ℕ) :
    (complex H).topDegree d (vertex H g i) ≤ Nat.card (H i) * Nat.choose n d := by
  calc
    _ ≤ (Finset.univ.biUnion (fun h : H i =>
        incidentInChamber H (g * h) (vertex H g i) d)).card :=
      Finset.card_le_card (incident_faces_subset H g i d)
    _ ≤ ∑ h : H i, (incidentInChamber H (g * h) (vertex H g i) d).card :=
      Finset.card_biUnion_le
    _ = Nat.card (H i) * Nat.choose n d := by
      have hc (h : H i) : vertex H g i ∈ chamber H (g * h) := by
        rw [(vertex_eq_iff H g (g * h) i).mpr (by simp)]
        exact vertex_mem_chamber _ _ _
      simp_rw [card_incidentInChamber H _ _ d (hc _)]
      simp [Nat.card_eq_fintype_card]

end

end CoboundaryExpanders.CosetConstruction

namespace CoboundaryExpanders.Construction

section
open Filter CosetConstruction _root_.OAI.CoboundaryExpanders.Complex
variable (p n : ℕ) [Fact p.Prime]

theorem localBound_pos : 0 < localBound p n := Nat.card_pos

theorem finiteCosetComplex_pure (hn : 1 ≤ n) (m : ℕ) :
    (finiteCosetComplex p n hn m).Pure n := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  exact CosetConstruction.pure _

theorem finiteCosetComplex_degree (hn : 1 ≤ n) (m d : ℕ)
    (v : Fin (finiteCosetComplex p n hn m).vertexCount) :
    (finiteCosetComplex p n hn m).topDegree d v ≤ localBound p n * Nat.choose n d := by
  let : Fintype (Gquot p (n + 1) m) := Fintype.ofFinite _
  obtain ⟨i, g, rfl⟩ := vertex_surjective (reducedLocalGroup p n hn m) v
  exact (topDegree_le _ _ _ _).trans
    (Nat.mul_le_mul_right _ (reducedLocalGroup_card_le p n hn m i))

end

open Filter _root_.OAI.CoboundaryExpanders.Complex

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Complex

theorem cofaceCount_le_topDegree {X : Complex} {i : ℕ} (σ : X.Face i)
    (n : ℕ) (v : Fin X.vertexCount) (hv : v ∈ σ.val) :
    X.cofaceCount n σ.val ≤ X.topDegree n v := by
  apply Finset.card_le_card
  intro τ hτ
  obtain ⟨hτ, hστ⟩ := Finset.mem_filter.mp hτ
  exact Finset.mem_filter.mpr ⟨hτ, hστ hv⟩

theorem cofaceCount_pos_of_pure {X : Complex} {n i : ℕ} (hX : X.Pure n)
    (σ : X.Face i) : 0 < X.cofaceCount n σ.val := by
  obtain ⟨τ,hτ,hστ⟩ := hX.2 σ.val (face_mem σ)
  exact Finset.card_pos.mpr ⟨τ,Finset.mem_filter.mpr ⟨hτ,hστ⟩⟩

theorem skeleton_cocycles {X : Complex} {s i : ℕ} (hi : i < s) :
    (X.skeletonCochainEquiv hi.le) '' X.cocycles i = (X.skeleton s).cocycles i := by
  ext f
  obtain ⟨f₀,rfl⟩ := (X.skeletonCochainEquiv hi.le).surjective f
  simp only [Set.mem_image, Set.mem_ofPred_eq, cocycles]
  constructor
  · rintro ⟨g,hg,he⟩
    have hg₀ : g = f₀ := (X.skeletonCochainEquiv hi.le).injective he
    subst g
    rw [X.skeleton_coboundary hi, hg, map_zero]
  · intro hf
    rw [X.skeleton_coboundary hi] at hf
    exact ⟨f₀, (X.skeletonCochainEquiv hi).injective (by simpa using hf), rfl⟩

theorem skeleton_cosystolic_iff {X : Complex} {s i : ℕ} (hi : i < s) (η : ℝ) :
    (∀ f : (X.skeleton s).Cochain i,
      η * (X.skeleton s).distance s i f ((X.skeleton s).cocycles i) ≤
        (X.skeleton s).norm s (i+1) ((X.skeleton s).coboundary i f)) ↔
    (∀ f : X.Cochain i,
      η * X.distance s i f (X.cocycles i) ≤ X.norm s (i+1) (X.coboundary i f)) := by
  constructor
  · intro h f
    have hh := h (X.skeletonCochainEquiv hi.le f)
    rw [← skeleton_cocycles hi, skeleton_distance_image,
      skeleton_coboundary X hi, skeleton_norm] at hh
    exact hh
  · intro h f
    obtain ⟨f₀,rfl⟩ := (X.skeletonCochainEquiv hi.le).surjective f
    rw [← skeleton_cocycles hi, skeleton_distance_image,
      skeleton_coboundary X hi, skeleton_norm]
    exact h f₀

end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.Construction
open _root_.OAI.CoboundaryExpanders.Complex Filter
variable (p n : ℕ) [Fact p.Prime]

theorem finiteCosetComplex_coface_bounds (hn : 1 ≤ n) (m i : ℕ)
    (σ : (finiteCosetComplex p n hn m).Face i) :
    1 ≤ ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ∧
    ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ≤ localBound p n := by
  constructor
  · exact_mod_cast cofaceCount_pos_of_pure (finiteCosetComplex_pure p n hn m) σ
  · have hp : σ.val.Nonempty := Finset.card_pos.mp (by rw [face_card σ]; omega)
    obtain ⟨v,hv⟩ := hp
    have h := (cofaceCount_le_topDegree σ n v hv).trans
      (finiteCosetComplex_degree p n hn m n v)
    simpa only [Nat.choose_self, Nat.mul_one] using (show
      ((finiteCosetComplex p n hn m).cofaceCount n σ.val : ℝ) ≤
        (localBound p n * Nat.choose n n : ℕ) from by exact_mod_cast h)

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Skeleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Skeleton-weight identities and conversion of raw cosystolic estimates to the finite weighted norms.
-/

section
open scoped BigOperators
open Filter

namespace CoboundaryExpanders.FatLadders
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
omit [Fintype V] [Fintype W] in
lemma delta_image (e : V ≃ W) (f : Finset W → k) (s : Finset V) :
    delta (fun t => f (t.image e)) s = delta f (s.image e) := by
  unfold delta
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    change f ((s.erase x).image e) = _
    rw [Finset.image_erase e.injective]
  · exact fun _ _ _ _ h => e.injective h

lemma norm_image (e : V ≃ W) (w : Finset W → ℝ) (f : Finset W → k) (r : ℕ) :
    norm (fun t => w (t.image e)) r (fun t => f (t.image e)) = norm w r f := by
  unfold norm
  apply Finset.sum_bij (fun s _ => s.image e)
  · intro s hs
    simpa only [mem_level,Finset.card_image_of_injective _ e.injective] using hs
  · intro s hs t ht h
    exact Finset.image_injective e.injective h
  · intro s hs
    refine ⟨s.image e.symm,?_,?_⟩
    · simpa only [mem_level,Finset.card_image_of_injective _ e.symm.injective] using hs
    · simp only [Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
  · intro s hs
    rfl
end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.Complex

section
variable (X : Complex)

attribute [local instance] OAI.CoboundaryExpanders.Complex.instFintypeFace_4
lemma coboundary_ofRaw (i : ℕ) (f : Finset (Fin X.vertexCount) → ZMod 2) :
    X.coboundary i (X.ofRaw i f) = X.ofRaw (i+1) (FatLadders.delta f) := by
  ext t
  change (∑ s : X.Face i, if s.val ⊆ t.val then f s.val else 0) = ∑ x ∈ t.val, f (t.val.erase x)
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun x hx => (⟨t.val.erase x,(mem_facesOf X i _).mpr
    ⟨X.downward (face_mem t) (Finset.erase_subset _ _),by rw [Finset.card_erase_of_mem hx,face_card t]; omega⟩⟩ : X.Face i))
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact Finset.erase_subset _ _
  · intro x hx y hy hxy
    exact (Finset.erase_inj t.val hx).mp (congrArg Subtype.val hxy)
  · intro s hs
    have hst : s.val ⊆ t.val := (Finset.mem_filter.mp hs).2
    have hcard : (t.val \ s.val).card = 1 := by
      rw [Finset.card_sdiff_of_subset hst,face_card t,face_card s]; omega
    obtain ⟨x,hx,he⟩ := (Finset.covBy_iff_card_sdiff_eq_one.mpr ⟨hst,hcard⟩).exists_finset_erase
    exact ⟨x,hx,Subtype.ext he⟩
  · intro x hx
    rfl

lemma cofaceCount_zero_of_not_mem (n : ℕ) {s : Finset (Fin X.vertexCount)}
    (hs : s ∉ X.faces) : X.cofaceCount n s = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
  exact hs (X.downward ((mem_facesOf X n t).mp ht).1 hst)

lemma norm_ofRaw (n i : ℕ) (f : Finset (Fin X.vertexCount) → ZMod 2) :
    X.norm n i (X.ofRaw i f) =
      FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+1) f /
        ((Nat.choose (n+1) (i+1) : ℝ)*(X.facesOf n).card) := by
  rw [norm]
  have he : (∑ s : X.Face i, if f s.val = 0 then (0:ℝ) else X.cofaceCount n s.val) =
      FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+1) f := by
    rw [sum_face_eq X i (fun s => if f s = 0 then (0:ℝ) else X.cofaceCount n s)]
    unfold FatLadders.norm FatLadders.atom
    apply Finset.sum_subset
    · intro s hs
      exact FatLadders.mem_level.mpr ((mem_facesOf X i s).mp hs).2
    · intro s hs hnot
      have hsm : s ∉ X.faces := by
        intro hm
        exact hnot ((mem_facesOf X i s).mpr ⟨hm,FatLadders.mem_level.mp hs⟩)
      rw [X.cofaceCount_zero_of_not_mem n hsm]
      simp
  rw [←he,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  change (if f s.val ≠ 0 then X.weight n i s else 0) = _
  rw [weight_eq_cofaceCount]
  by_cases hf : f s.val = 0 <;> simp [hf]

lemma normalizer_pos {n i : ℕ} (hX : X.Pure n) (hi : i ≤ n) :
    0 < (Nat.choose (n+1) (i+1) : ℝ)*(X.facesOf n).card := by
  exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (by omega))) (Nat.cast_pos.mpr hX.1.card_pos)

end

variable {X : Complex}
lemma raw_norm_eq_mul {n i : ℕ} (hX : X.Pure n) (hi : i ≤ n)
    (f : Finset (Fin X.vertexCount) → ZMod 2) :
    FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+1) f =
      ((Nat.choose (n+1) (i+1) : ℝ)*(X.facesOf n).card)*X.norm n i (X.ofRaw i f) := by
  rw [X.norm_ofRaw]
  exact (mul_div_cancel₀ _ (X.normalizer_pos hX hi).ne').symm

theorem cosystolic_of_raw {n i : ℕ} (hX : X.Pure n) (hi : i < n) {K : ℝ} (hK : 0 < K)
    (hraw : ∀ f : Finset (Fin X.vertexCount) → ZMod 2, ∃ h,
      FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+2) (FatLadders.delta (f+h)) = 0 ∧
      FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+1) h ≤
        K*FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+2) (FatLadders.delta f))
    (f : X.Cochain i) :
    (1/(K*2^(n+1))) * X.distance n i f (X.cocycles i) ≤ X.norm n (i+1) (X.coboundary i f) := by
  obtain ⟨h,hz,hb⟩ := hraw (X.rawCochain i f)
  have hdelta : X.coboundary i f = X.ofRaw (i+1) (FatLadders.delta (X.rawCochain i f)) := by
    simpa only [ofRaw_rawCochain] using X.coboundary_ofRaw i (X.rawCochain i f)
  have hz' : X.coboundary i (f+X.ofRaw i h) = 0 := by
    apply (norm_eq_zero_iff hX (by omega) _).mp
    rw [←X.ofRaw_rawCochain i f,←X.ofRaw_add,X.coboundary_ofRaw,X.norm_ofRaw]
    simp only [Nat.add_assoc,show 1+1=2 by rfl,hz,zero_div]
  have hn : X.norm n i (X.ofRaw i h) ≤ K*2^(n+1)*X.norm n (i+1) (X.coboundary i f) := by
    rw [raw_norm_eq_mul hX (by omega),raw_norm_eq_mul hX (by omega),←hdelta] at hb
    have hc0 : 1 ≤ (Nat.choose (n+1) (i+1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (show i+1 ≤ n+1 by omega)
    have hc1 : (Nat.choose (n+1) (i+1+1) : ℝ) ≤ 2^(n+1) := by
      exact_mod_cast Nat.choose_le_two_pow (n+1) (i+1+1)
    have hbound : (Nat.choose (n+1) (i+1+1) : ℝ) ≤ 2^(n+1)*(Nat.choose (n+1) (i+1) : ℝ) :=
      hc1.trans (by nlinarith [show (0:ℝ) ≤ 2^(n+1) by positivity])
    apply (mul_le_mul_iff_right₀ (X.normalizer_pos (i:=i) hX (by omega))).mp
    apply hb.trans
    have hcnt : (0:ℝ) ≤ (X.facesOf n).card := Nat.cast_nonneg _
    have hx := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hbound hcnt) hK.le) (X.norm_nonneg n (i+1) (X.coboundary i f))
    nlinarith only [hx]
  have hd : X.distance n i f (X.cocycles i) ≤ X.norm n i (X.ofRaw i h) := by
    have hmem : f+X.ofRaw i h ∈ X.cocycles i := hz'
    have hh := X.distance_le_norm n i f hmem
    have he : f-(f+X.ofRaw i h) = X.ofRaw i h := by
      ext s
      simp only [Pi.sub_apply,Pi.add_apply,sub_add_cancel_left,CharTwo.neg_eq]
    rwa [he] at hh
  have hpos : 0 < K*2^(n+1) := mul_pos hK (by positivity)
  have hh := hd.trans hn
  apply (mul_le_mul_iff_right₀ hpos).mp
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.FatLadders
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
lemma correction_image (e : V ≃ W) (wV : Finset V → ℝ) (wW : Finset W → ℝ)
    (hw : ∀ s,wW (s.image e) = wV s) (r : ℕ) (K : ℝ)
    (hh : ∀ f : Finset V → k, ∃ h,
      norm wV r (delta (f+h)) = 0 ∧ norm wV (r-1) h ≤ K*norm wV r (delta f)) :
    ∀ f : Finset W → k, ∃ h,
      norm wW r (delta (f+h)) = 0 ∧ norm wW (r-1) h ≤ K*norm wW r (delta f) := by
  intro f
  obtain ⟨h,hz,hb⟩ := hh (fun s => f (s.image e))
  let g : Finset W → k := fun s => h (s.image e.symm)
  have hg : (fun s => g (s.image e)) = h := by
    funext s
    simp only [g,Finset.image_image,Function.comp_def,Equiv.symm_apply_apply,Finset.image_id']
  have norm_transfer : ∀ r (F : Finset W → k),
      norm wV r (fun s => F (s.image e)) = norm wW r F := by
    intro r F
    have he : wV = fun s => wW (s.image e) := (funext hw).symm
    rw [he]
    exact norm_image e wW F r
  have hz' := norm_transfer r (delta (f+g))
  have hd : (fun s => delta (f+g) (s.image e)) = delta ((fun s => f (s.image e))+h) := by
    funext s
    rw [←delta_image e]
    congr 1
    funext t
    change f (t.image e)+g (t.image e) = f (t.image e)+h t
    rw [congrFun hg t]
  refine ⟨g,?_,?_⟩
  · rwa [←hz',hd]
  · rw [←norm_transfer (r-1) g,←norm_transfer r (delta f),hg]
    have hd' : (fun s => delta f (s.image e)) = delta (fun s => f (s.image e)) :=
      funext (fun s => (delta_image e f s).symm)
    rwa [hd']
end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.CosetConstruction

open InfiniteChains.FiniteWeights
variable {G : Type} [Group G] [Fintype G] {n : ℕ}
variable (H : Fin (n+1) → Subgroup G)

lemma labelled_cofaces (r : ℕ) (s : Finset (Vertex H)) :
    (complex H).cofaceCount r (s.image (labelEquiv H)) =
      cofaces (TypedCosetFaces.complex H) (r+1) s := by
  unfold Complex.cofaceCount cofaces
  symm
  apply Finset.card_bij (fun t _ => t.image (labelEquiv H))
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    exact Finset.mem_filter.mpr ⟨(Complex.mem_facesOf _ _ _).mpr
      ⟨(labelled_mem_faces H t).mpr ht,by rwa [Finset.card_image_of_injective _ (labelEquiv H).injective]⟩,
      Finset.image_subset_image hst⟩
  · intro t ht u hu he
    exact Finset.image_injective (labelEquiv H).injective he
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (Complex.mem_facesOf _ _ _).mp ht
    have he : (t.image (labelEquiv H).symm).image (labelEquiv H) = t := by
      simp only [Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
    refine ⟨t.image (labelEquiv H).symm,Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr ⟨?_,?_⟩,?_⟩,he⟩
    · apply (labelled_mem_faces H _).mp
      rwa [he]
    · rwa [Finset.card_image_of_injective _ (labelEquiv H).symm.injective]
    · apply (Finset.image_subset_image_iff (labelEquiv H).injective).mp
      rwa [he]

theorem cosystolic_of_typed_raw (i : ℕ) (hi : i < n) {K : ℝ} (hK : 0 < K)
    (hh : ∀ f : Finset (Vertex H) → ZMod 2, ∃ h,
      FatLadders.norm (fun s => (cofaces (TypedCosetFaces.complex H) (n+1) s : ℝ)) (i+2)
        (FatLadders.delta (f+h)) = 0 ∧
      FatLadders.norm (fun s => (cofaces (TypedCosetFaces.complex H) (n+1) s : ℝ)) (i+1) h ≤
        K*FatLadders.norm (fun s => (cofaces (TypedCosetFaces.complex H) (n+1) s : ℝ)) (i+2)
          (FatLadders.delta f)) :
    ∀ f : (complex H).Cochain i,
      (1/(K*2^(n+1))) * (complex H).distance n i f ((complex H).cocycles i) ≤
        (complex H).norm n (i+1) ((complex H).coboundary i f) := by
  apply Complex.cosystolic_of_raw (pure H) hi hK
  have he := FatLadders.correction_image (labelEquiv H)
    (fun s => (cofaces (TypedCosetFaces.complex H) (n+1) s : ℝ))
    (fun s => ((complex H).cofaceCount n s : ℝ))
    (fun s => by rw [labelled_cofaces]) (i+2) K
  simpa only [show i+2-1=i+1 by omega] using he hh
end CoboundaryExpanders.CosetConstruction

end

namespace CoboundaryExpanders.Complex

theorem skeleton_cosystolic_of_ambient {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (hi : i < s) (hs : s ≤ n) {M η : ℝ}
    (hM : 0 < M) (hη : 0 ≤ η)
    (hc : ∀ ρ : X.Face s, 1 ≤ (X.cofaceCount n ρ.val : ℝ) ∧
      (X.cofaceCount n ρ.val : ℝ) ≤ M)
    (hquant : ∀ f : X.Cochain i,
      η * X.distance n i f (X.cocycles i) ≤ X.norm n (i+1) (X.coboundary i f))
    (f : X.Cochain i) :
    (η/M) * X.distance s i f (X.cocycles i) ≤ X.norm s (i+1) (X.coboundary i f) := by
  have hZ : (X.cocycles i).Nonempty := ⟨0, by simp [cocycles]⟩
  have hdist := (skeleton_distance_comparison hX hi.le hs zero_lt_one hc f hZ).2
  have hnorm := (skeleton_norm_comparison hX hi hs zero_lt_one hc (X.coboundary i f)).1
  simp only [div_one] at hdist
  calc
    (η/M) * X.distance s i f (X.cocycles i) ≤
        (η/M) * (X.skeletonScale n s * X.distance n i f (X.cocycles i)) :=
      mul_le_mul_of_nonneg_left hdist (div_nonneg hη hM.le)
    _ = (X.skeletonScale n s/M) * (η * X.distance n i f (X.cocycles i)) := by ring
    _ ≤ (X.skeletonScale n s/M) * X.norm n (i+1) (X.coboundary i f) :=
      mul_le_mul_of_nonneg_left (hquant f) (div_nonneg (skeletonScale_pos hX hs).le hM.le)
    _ ≤ _ := hnorm
end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.Construction
open InfiniteChains.FiniteWeights

theorem actual_uniform_cosystolic_oai (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p → UniformCosystolic p n (by omega) := by
  obtain ⟨Q,K,hK,hraw⟩ := uniform_actual_raw_cosystolic n hn
  refine ⟨Q,?_⟩
  intro p hp hqp
  have hM : 0 < (localBound p n : ℝ) := by exact_mod_cast localBound_pos p n
  have heta : 0 < (1/(K*2^(n+1)) : ℝ) := by positivity
  refine ⟨(1/(K*2^(n+1)))/(localBound p n),div_pos heta hM,?_⟩
  intro m hm i hi
  apply (Complex.skeleton_cosystolic_iff hi _).mpr
  apply Complex.skeleton_cosystolic_of_ambient (finiteCosetComplex_pure p n (by omega) m) hi
    (by omega) hM heta.le (finiteCosetComplex_coface_bounds p n (by omega) m (n-1))
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  apply CosetConstruction.cosystolic_of_typed_raw (reducedLocalGroup p n (by omega) m) i (by omega) hK
  exact hraw p hp hqp m hm (i+2) (by omega)
end CoboundaryExpanders.Construction

end

end OAI
end

theorem solution : type_of% @OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic_oai := @OAI.CoboundaryExpanders.Construction.actual_uniform_cosystolic_oai
