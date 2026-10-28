-- Prove2me | solution 1 for OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:57:51.908407+00:00
-- url     : https://prove2.me/submissions/e9439614-c3e9-4bbe-9fc7-aad981511a21

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000
import Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_arbitraryEndpoint_tendsto_of_grids
import Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_characteristic_lengths_exist
import Theorems.Thm_OAI_GammaFPP_IntervalTravelBridge_gamma_moving_goodOrigin_failure_tendsto

section
-- module Solutions.OAIW2_GammaFPP.Compat
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_ProbabilityFoundations
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem measurableSet_strict_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds < bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_lt (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

theorem measurableSet_bounded_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds ≤ bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_le (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_CoordinateTails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

theorem straightEdge_injective (p : Vertex) (d : Step) :
    Function.Injective (straightEdge p d) := by
  intro i j h
  cases d <;> simp [straightEdge, Step.edge, Step.delta, Prod.ext_iff] at h <;> omega

theorem pathCost_replicate (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ i ∈ range n, w (straightEdge p d i) := by
  induction n generalizing p with
  | zero => simp [pathCost]
  | succ n ih =>
    rw [List.replicate_succ, pathCost, ih, sum_range_succ']
    simp [straightEdge, Nat.cast_add, add_smul, add_assoc, add_comm]

theorem pathCost_replicate_edgeSet (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ e ∈ (range n).image (straightEdge p d), w e := by
  rw [sum_image (fun i _ j _ hij => straightEdge_injective p d hij)]
  exact pathCost_replicate w p d n

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_SpatialModulus
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

theorem latticeBox_card (n : ℕ) : (latticeBox n).card = (2*n+1)^2 := by
  have hi : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp [latticeBox, hi, pow_two]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem summable_box_connection_bound {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => (2*(n : ℝ)+1)^4 * (2 * Real.exp (-ε*n/4))) := by
  have hs (k : ℕ) := Real.summable_pow_mul_exp_neg_nat_mul k
    (show 0 < ε/4 by linarith)
  have ht := (((((hs 4).mul_left 32).add ((hs 3).mul_left 64)).add
    ((hs 2).mul_left 48)).add ((hs 1).mul_left 16)).add ((hs 0).mul_left 2)
  apply ht.congr
  intro n
  simp only [pow_one, pow_zero]
  have he : -(ε/4)*(n : ℝ) = -ε*n/4 := by ring
  rw [he]
  ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKFamilies
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

lemma mem_disjointOccurrenceFamily (s : Finset α) (A B : Finset (Finset α)) (x : Finset α) :
    x ∈ disjointOccurrenceFamily s A B ↔
      x ⊆ s ∧ ∃ a ∈ A, ∃ b ∈ B, a ⊆ x ∧ b ⊆ x ∧ Disjoint a b := by
  classical
  simp [disjointOccurrenceFamily]

lemma disjointOccurrenceFamily_mono (s : Finset α) {A A' B B' : Finset (Finset α)}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    disjointOccurrenceFamily s A B ⊆ disjointOccurrenceFamily s A' B' := by
  intro x hx
  obtain ⟨hs,a,ha,b,hb,hax,hbx,hab⟩ := (mem_disjointOccurrenceFamily ..).mp hx
  exact (mem_disjointOccurrenceFamily ..).mpr ⟨hs,a,hA ha,b,hB hb,hax,hbx,hab⟩

lemma UpwardFamily.nonMember {s : Finset α} {A : Finset (Finset α)} {e : α}
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) :
    UpwardFamily s (A.nonMemberSubfamily e) := by
  constructor
  · intro x hx
    obtain ⟨hx,he'⟩ := mem_nonMemberSubfamily.mp hx
    exact (subset_insert_iff_of_notMem he').mp (hA.1 x hx)
  · intro x hx y hxy hys
    obtain ⟨hx,hex⟩ := mem_nonMemberSubfamily.mp hx
    exact mem_nonMemberSubfamily.mpr ⟨hA.2 x hx y hxy (hys.trans (subset_insert _ _)),
      fun hey => he (hys hey)⟩

lemma UpwardFamily.member {s : Finset α} {A : Finset (Finset α)} {e : α}
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) :
    UpwardFamily s (A.memberSubfamily e) := by
  constructor
  · intro x hx
    obtain ⟨hx,hex⟩ := mem_memberSubfamily.mp hx
    exact (subset_insert_iff_of_notMem hex).mp ((subset_insert _ _).trans (hA.1 _ hx))
  · intro x hx y hxy hys
    obtain ⟨hx,hex⟩ := mem_memberSubfamily.mp hx
    exact mem_memberSubfamily.mpr ⟨hA.2 _ hx _ (insert_subset_insert _ hxy)
      (insert_subset_insert _ hys),fun hey => he (hys hey)⟩

lemma UpwardFamily.slice_subset {s : Finset α} {A : Finset (Finset α)} {e : α}
    (hA : UpwardFamily (insert e s) A) : A.nonMemberSubfamily e ⊆ A.memberSubfamily e := by
  intro x hx
  obtain ⟨hx,hex⟩ := mem_nonMemberSubfamily.mp hx
  exact mem_memberSubfamily.mpr ⟨hA.2 x hx _ (subset_insert _ _)
    (by intro y hy; rcases mem_insert.mp hy with rfl | hy; exact mem_insert_self _ _; exact hA.1 x hx hy),hex⟩

lemma disjointOccurrence_nonMember (s : Finset α) (A B : Finset (Finset α)) (e : α) (he : e ∉ s) :
    (disjointOccurrenceFamily (insert e s) A B).nonMemberSubfamily e =
      disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.nonMemberSubfamily e) := by
  ext x
  simp only [mem_nonMemberSubfamily,mem_disjointOccurrenceFamily]
  constructor
  · rintro ⟨⟨hxs,a,ha,b,hb,hax,hbx,hab⟩,hex⟩
    exact ⟨(subset_insert_iff_of_notMem hex).mp hxs,a,⟨ha,fun he => hex (hax he)⟩,
      b,⟨hb,fun he => hex (hbx he)⟩,hax,hbx,hab⟩
  · rintro ⟨hxs,a,⟨ha,hea⟩,b,⟨hb,heb⟩,hax,hbx,hab⟩
    refine ⟨⟨hxs.trans (subset_insert _ _),a,ha,b,hb,hax,hbx,hab⟩,?_⟩
    exact fun hex => he (hxs hex)

lemma erase_subset_of_subset_insert {e : α} {a x : Finset α} (ha : a ⊆ insert e x) :
    a.erase e ⊆ x := by
  intro v hv
  obtain ⟨hne,hva⟩ := mem_erase.mp hv
  exact (mem_insert.mp (ha hva)).resolve_left hne

lemma disjointOccurrence_member (s : Finset α) (A B : Finset (Finset α)) (e : α)
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) (hB : UpwardFamily (insert e s) B) :
    (disjointOccurrenceFamily (insert e s) A B).memberSubfamily e =
      disjointOccurrenceFamily s (A.memberSubfamily e) (B.nonMemberSubfamily e) ∪
      disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.memberSubfamily e) := by
  ext x
  simp only [mem_memberSubfamily,mem_union,mem_disjointOccurrenceFamily]
  constructor
  · rintro ⟨⟨hxs,a,ha,b,hb,hax,hbx,hab⟩,hex⟩
    have hxs' : x ⊆ s := (subset_insert_iff_of_notMem hex).mp ((subset_insert _ _).trans hxs)
    by_cases hea : e ∈ a
    · have heb : e ∉ b := fun hb' => Finset.disjoint_left.mp hab hea hb'
      left
      refine ⟨hxs',a.erase e,?_,b,mem_nonMemberSubfamily.mpr ⟨hb,heb⟩,erase_subset_of_subset_insert hax,?_,?_⟩
      · exact ⟨by simpa [insert_erase hea] using ha,notMem_erase _ _⟩
      · exact (subset_insert_iff_of_notMem heb).mp hbx
      · exact hab.mono_left (erase_subset _ _)
    · right
      refine ⟨hxs',a,mem_nonMemberSubfamily.mpr ⟨ha,hea⟩,b.erase e,?_,
        (subset_insert_iff_of_notMem hea).mp hax,erase_subset_of_subset_insert hbx,?_⟩
      · refine ⟨hB.2 b hb _ (by intro v hv; by_cases heq : v=e; exact mem_insert.mpr (Or.inl heq); exact mem_insert.mpr (Or.inr (mem_erase.mpr ⟨heq,hv⟩))) ?_,notMem_erase _ _⟩
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact mem_insert_self _ _
        · exact hB.1 b hb (mem_of_mem_erase hv)
      · exact hab.mono_right (erase_subset _ _)
  · intro hx
    rcases hx with ⟨hxs,a,⟨ha,hea⟩,b,hb,hax,hbx,hab⟩ | ⟨hxs,a,ha,b,⟨hb,heb⟩,hax,hbx,hab⟩
    · obtain ⟨hb,heb⟩ := mem_nonMemberSubfamily.mp hb
      refine ⟨⟨insert_subset_insert _ hxs,insert e a,ha,b,hb,
        insert_subset_insert _ hax,hbx.trans (subset_insert _ _),?_⟩,fun h => he (hxs h)⟩
      exact Finset.disjoint_insert_left.mpr ⟨heb,hab⟩
    · obtain ⟨ha,hea⟩ := mem_nonMemberSubfamily.mp ha
      refine ⟨⟨insert_subset_insert _ hxs,a,ha,insert e b,hb,
        hax.trans (subset_insert _ _),insert_subset_insert _ hbx,?_⟩,fun h => he (hxs h)⟩
      exact Finset.disjoint_insert_right.mpr ⟨hea,hab⟩

theorem finite_fair_BK (s : Finset α) (A B : Finset (Finset α))
    (hA : UpwardFamily s A) (hB : UpwardFamily s B) :
    2^s.card*(disjointOccurrenceFamily s A B).card ≤ A.card*B.card := by
  classical
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    have hAs := hA.1
    have hBs := hB.1
    simp_rw [subset_empty,← subset_singleton_iff',subset_singleton_iff] at hAs hBs
    rcases hAs with rfl | rfl <;> rcases hBs with rfl | rfl <;>
      simp [disjointOccurrenceFamily]
  | @insert e s he ih =>
    let D₀ := disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.nonMemberSubfamily e)
    let D₁ := disjointOccurrenceFamily s (A.memberSubfamily e) (B.nonMemberSubfamily e)
    let D₂ := disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.memberSubfamily e)
    have h₀₁ : D₀ ⊆ D₁ := disjointOccurrenceFamily_mono s hA.slice_subset (Subset.rfl)
    have h₀₂ : D₀ ⊆ D₂ := disjointOccurrenceFamily_mono s (Subset.rfl) hB.slice_subset
    have hcount : (disjointOccurrenceFamily (insert e s) A B).card ≤ D₁.card+D₂.card := by
      rw [← card_memberSubfamily_add_card_nonMemberSubfamily e,
        disjointOccurrence_member s A B e he hA hB,disjointOccurrence_nonMember s A B e he]
      have hh := Finset.card_le_card (subset_inter h₀₁ h₀₂)
      have hu := Finset.card_union_add_card_inter D₁ D₂
      change (D₁ ∪ D₂).card+D₀.card ≤ D₁.card+D₂.card
      omega
    have h₁ := ih _ _ (hA.member he) (hB.nonMember he)
    have h₂ := ih _ _ (hA.nonMember he) (hB.member he)
    have hca := Finset.card_le_card hA.slice_subset
    have hcb := Finset.card_le_card hB.slice_subset
    have hcross := mul_add_mul_le_mul_add_mul hca hcb
    have ha := card_memberSubfamily_add_card_nonMemberSubfamily e A
    have hb := card_memberSubfamily_add_card_nonMemberSubfamily e B
    have hmul := Nat.mul_le_mul_left (2^s.card) hcount
    rw [Finset.card_insert_of_notMem he,pow_succ]
    dsimp [D₁,D₂] at hmul
    nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKRepeated
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

lemma upward_disjointOccurrence (s : Finset α) (A B : Finset (Finset α)) :
    UpwardFamily s (disjointOccurrenceFamily s A B) := by
  constructor
  · intro x hx
    exact ((mem_disjointOccurrenceFamily ..).mp hx).1
  · intro x hx y hxy hys
    obtain ⟨_,a,ha,b,hb,hax,hbx,hab⟩ := (mem_disjointOccurrenceFamily ..).mp hx
    exact (mem_disjointOccurrenceFamily ..).mpr ⟨hys,a,ha,b,hb,hax.trans hxy,hbx.trans hxy,hab⟩

omit [DecidableEq α] in
lemma fairFamilyMass_nonneg (s : Finset α) (A : Finset (Finset α)) :
    0 ≤ fairFamilyMass s A := by unfold fairFamilyMass; positivity

omit [DecidableEq α] in
lemma fairFamilyMass_mono (s : Finset α) {A B : Finset (Finset α)} (h : A ⊆ B) :
    fairFamilyMass s A ≤ fairFamilyMass s B := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (by positivity)

omit [DecidableEq α] in
lemma fairFamilyMass_powerset (s : Finset α) : fairFamilyMass s s.powerset = 1 := by
  simp [fairFamilyMass,Finset.card_powerset]

lemma finite_fair_BK_mass (s : Finset α) (A B : Finset (Finset α))
    (hA : UpwardFamily s A) (hB : UpwardFamily s B) :
    fairFamilyMass s (disjointOccurrenceFamily s A B) ≤ fairFamilyMass s A * fairFamilyMass s B := by
  have h := finite_fair_BK s A B hA hB
  have hr : (2:ℝ)^s.card * (disjointOccurrenceFamily s A B).card ≤ (A.card:ℝ)*B.card := by
    exact_mod_cast h
  unfold fairFamilyMass
  rw [div_mul_div_comm,div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) s.card]

lemma upward_iteratedDisjointOccurrence (s : Finset α) (As : List (Finset (Finset α))) :
    UpwardFamily s (iteratedDisjointOccurrence s As) := by
  cases As with
  | nil =>
    constructor
    · intro x hx; exact mem_powerset.mp hx
    · intro x hx y hxy hys; exact mem_powerset.mpr hys
  | cons A As => exact upward_disjointOccurrence s A _

theorem finite_fair_BK_repeated (s : Finset α) (As : List (Finset (Finset α)))
    (hAs : ∀ A ∈ As, UpwardFamily s A) :
    fairFamilyMass s (iteratedDisjointOccurrence s As) ≤ (As.map (fairFamilyMass s)).prod := by
  induction As with
  | nil => simp [iteratedDisjointOccurrence,fairFamilyMass_powerset]
  | cons A As ih =>
    have hA := hAs A (List.mem_cons_self ..)
    have htail : ∀ B ∈ As, UpwardFamily s B := fun B hB => hAs B (List.mem_cons_of_mem _ hB)
    exact (finite_fair_BK_mass s A _ hA (upward_iteratedDisjointOccurrence s As)).trans
      (by simpa using mul_le_mul_of_nonneg_left (ih htail) (fairFamilyMass_nonneg s A))

lemma mem_foldr_union (ws : List (Finset α)) (a : α) :
    a ∈ ws.foldr (· ∪ ·) ∅ ↔ ∃ v ∈ ws, a ∈ v := by
  induction ws with
  | nil => simp
  | cons v vs ih => simp [ih]

theorem certificates_mem_iterated (s : Finset α) (As : List (Finset (Finset α)))
    (ws : List (Finset α)) (x : Finset α) (hxs : x ⊆ s)
    (hmem : List.Forall₂ (fun w A => w ∈ A) ws As)
    (hdis : ws.Pairwise Disjoint) (hsub : ∀ w ∈ ws, w ⊆ x) :
    x ∈ iteratedDisjointOccurrence s As := by
  induction hmem generalizing x with
  | nil => exact mem_powerset.mpr hxs
  | @cons w A ws As hw hmem ih =>
    have hd := List.pairwise_cons.mp hdis
    let u : Finset α := ws.foldr (· ∪ ·) ∅
    have hu : ∀ a, a ∈ u ↔ ∃ v ∈ ws, a ∈ v := mem_foldr_union ws
    have hux : u ⊆ x := by
      intro a ha
      obtain ⟨v,hv,hav⟩ := (hu a).mp ha
      exact hsub v (List.mem_cons_of_mem _ hv) hav
    have htail : ∀ v ∈ ws, v ⊆ u := by
      intro v hv a ha
      exact (hu a).mpr ⟨v,hv,ha⟩
    have hwu : Disjoint w u := by
      apply Finset.disjoint_left.mpr
      intro a haw hau
      obtain ⟨v,hv,hav⟩ := (hu a).mp hau
      exact Finset.disjoint_left.mp (hd.1 v hv) haw hav
    exact (mem_disjointOccurrenceFamily ..).mpr ⟨hxs,w,hw,u,
      ih u (hux.trans hxs) hd.2 htail,hsub w (List.mem_cons_self ..),hux,hwu⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_DyadicRanks
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open Finset PlanarFPP

lemma dyadicPositions_subset (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicPositions t x e ⊆ range t := by
  intro a ha
  obtain ⟨h,_,rfl⟩ := mem_image.mp ha
  rw [mem_range]
  have := h.isLt
  omega

lemma mem_dyadicPositions (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) (h : Fin t) :
    t-(h.val+1) ∈ dyadicPositions t x e ↔ (e,h) ∈ x := by
  constructor
  · intro hm
    obtain ⟨a,ha,he⟩ := mem_image.mp hm
    have heq : a=h := by apply Fin.ext; have := a.isLt; have := h.isLt; omega
    subst a
    exact (mem_filter.mp ha).2
  · intro hm
    exact mem_image.mpr ⟨h,mem_filter.mpr ⟨mem_univ _,hm⟩,rfl⟩

lemma sum_two_powers_range (t : ℕ) : (∑ a ∈ range t, 2^a)+1=2^t := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ,pow_succ]; omega

lemma dyadicRank_lt (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e < 2^t := by
  have h := sum_le_sum_of_subset_of_nonneg (f := fun a : ℕ => 2^a) (dyadicPositions_subset t x e)
    (fun _ _ _ => Nat.zero_le _)
  have hg := sum_two_powers_range t
  unfold dyadicRank
  omega

lemma dyadicRank_eq_iff (t : ℕ) (x y : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e = dyadicRank t y e ↔ ∀ h : Fin t, (e,h) ∈ x ↔ (e,h) ∈ y := by
  constructor
  · intro he
    have hp : dyadicPositions t x e = dyadicPositions t y e := by
      have hh := congrArg (fun n : ℕ => n.bitIndices.toFinset) he
      simpa [dyadicRank] using hh
    intro h
    rw [← mem_dyadicPositions t x e h,← mem_dyadicPositions t y e h,hp]
  · intro he
    have hp : dyadicPositions t x e = dyadicPositions t y e := by
      unfold dyadicPositions
      congr 1
      ext h
      simp [he h]
    simp [dyadicRank,hp]

lemma dyadicRanks_injective (S : Finset Edge) (t : ℕ) {x y : Finset (Edge × Fin t)}
    (hx : x ⊆ S ×ˢ univ) (hy : y ⊆ S ×ˢ univ)
    (h : ∀ e ∈ S, dyadicRank t x e = dyadicRank t y e) : x=y := by
  ext ⟨e,a⟩
  by_cases he : e ∈ S
  · exact (dyadicRank_eq_iff t x y e).mp (h e he) a
  · have hn : (e,a) ∉ x := fun hm => he (mem_product.mp (hx hm)).1
    have hn' : (e,a) ∉ y := fun hm => he (mem_product.mp (hy hm)).1
    simp [hn,hn']

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CDF
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {shape rate : ℝ}

lemma gamma_cdf_lt_one (hs : 0 < shape) (hr : 0 < rate)
    {x : ℝ} (hx : 0 ≤ x) : cdf (gammaMeasure shape rate) x < 1 := by
  have hlt := gamma_cdf_strictMonoOn hs hr hx
    (show 0 ≤ x + 1 by linarith) (show x < x + 1 by linarith)
  exact hlt.trans_le (cdf_le_one (gammaMeasure shape rate) (x + 1))

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Quantile
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma gammaQuantileReal_spec {shape rate u : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (hu : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ gammaQuantileReal shape rate hs hr u ∧
      cdf (gammaMeasure shape rate) (gammaQuantileReal shape rate hs hr u) = u := by
  simp only [gammaQuantileReal, dite_eq_left (show 0 ≤ u ∧ u < 1 from ⟨hu, hu1⟩)]
  exact Classical.choose_spec (ExistsUnique.exists (gamma_cdf_existsUnique hs hr hu hu1))

lemma gammaQuantileReal_nonneg {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (u : ℝ) : 0 ≤ gammaQuantileReal shape rate hs hr u := by
  by_cases hu : 0 ≤ u ∧ u < 1
  · exact (gammaQuantileReal_spec hs hr hu.1 hu.2).1
  · simp [gammaQuantileReal, hu]

lemma gammaQuantileReal_le_iff {shape rate u x : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (hu : 0 ≤ u) (hu1 : u < 1) (hx : 0 ≤ x) :
    gammaQuantileReal shape rate hs hr u ≤ x ↔ u ≤ cdf (gammaMeasure shape rate) x := by
  have hq := gammaQuantileReal_spec hs hr hu hu1
  constructor
  · intro h
    rw [← hq.2]
    exact monotone_cdf _ h
  · intro h
    by_contra hn
    have hh := gamma_cdf_strictMonoOn hs hr hx hq.1 (lt_of_not_ge hn)
    rw [hq.2] at hh
    exact (not_lt_of_ge h) hh

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SurvivalQuantile
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

lemma gammaSurvival_mem (hs : 0 < shape) (hr : 0 < rate) {x : ℝ} (hx : 0 ≤ x) :
    gammaSurvival shape rate x ∈ Ioc (0 : ℝ) 1 := by
  have h := gamma_cdf_lt_one hs hr hx
  have h' := cdf_nonneg (gammaMeasure shape rate) x
  constructor <;> dsimp [gammaSurvival] <;> linarith

lemma gammaQuantileReal_cdf {x : ℝ} (hx : 0 ≤ x) :
    gammaQuantileReal shape rate hs hr (cdf (gammaMeasure shape rate) x) = x := by
  have hq := gammaQuantileReal_spec hs hr (cdf_nonneg _ x) (gamma_cdf_lt_one hs hr hx)
  exact (gamma_cdf_strictMonoOn hs hr).injOn hq.1 hx hq.2

lemma gammaSurvivalQuantile_inverse {x : ℝ} (hx : 0 ≤ x) :
    gammaSurvivalQuantile hs hr (gammaSurvival shape rate x) = x := by
  simpa [gammaSurvivalQuantile, gammaSurvival] using gammaQuantileReal_cdf hs hr hx

lemma gammaSurvivalQuantile_antitoneOn :
    AntitoneOn (gammaSurvivalQuantile hs hr) (Ioc (0 : ℝ) 1) := by
  intro v hv w hw hvw
  have hvq := gammaQuantileReal_spec hs hr (show 0 ≤ 1-v by linarith [hv.2])
    (show 1-v < 1 by linarith [hv.1])
  apply (gammaQuantileReal_le_iff hs hr (show 0 ≤ 1-w by linarith [hw.2])
    (show 1-w < 1 by linarith [hw.1]) hvq.1).mpr
  rw [hvq.2]
  linarith

/-- Inverse continuity includes the one-sided probability endpoint zero.
The arbitrary real value at probability one is not used. -/
lemma gammaQuantileReal_continuousOn :
    ContinuousOn (gammaQuantileReal shape rate hs hr) (Ico (0 : ℝ) 1) := by
  intro u hu
  have hq := gammaQuantileReal_spec hs hr hu.1 hu.2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : 0 ≤ a
    · have hc : cdf (gammaMeasure shape rate) a < u := by
        have h := gamma_cdf_strictMonoOn hs hr ha0 hq.1 ha
        simpa only [hq.2] using h
      have he : ∀ᶠ v in 𝓝[Ico (0 : ℝ) 1] u, cdf (gammaMeasure shape rate) a < v :=
        (continuousWithinAt_id.tendsto).eventually (Ioi_mem_nhds hc)
      filter_upwards [he, self_mem_nhdsWithin] with v hv hvdom
      apply lt_of_not_ge
      intro hle
      have hh := (gammaQuantileReal_le_iff hs hr hvdom.1 hvdom.2 ha0).mp hle
      exact (not_le_of_gt hv) hh
    · exact Filter.Eventually.of_forall (fun v =>
        (lt_of_not_ge ha0).trans_le (gammaQuantileReal_nonneg hs hr v))
  · intro b hb
    have hb0 : 0 ≤ b := hq.1.trans hb.le
    have hc : u < cdf (gammaMeasure shape rate) b := by
      have h := gamma_cdf_strictMonoOn hs hr hq.1 hb0 hb
      simpa only [hq.2] using h
    have he : ∀ᶠ v in 𝓝[Ico (0 : ℝ) 1] u, v < cdf (gammaMeasure shape rate) b :=
      (continuousWithinAt_id.tendsto).eventually (Iio_mem_nhds hc)
    filter_upwards [he, self_mem_nhdsWithin] with v hv hvdom
    apply lt_of_not_ge
    intro hle
    have hh := monotone_cdf (gammaMeasure shape rate) hle
    rw [(gammaQuantileReal_spec hs hr hvdom.1 hvdom.2).2] at hh
    exact (not_le_of_gt hv) hh

lemma gammaSurvivalQuantile_continuousOn :
    ContinuousOn (gammaSurvivalQuantile hs hr) (Ioc (0 : ℝ) 1) := by
  apply (gammaQuantileReal_continuousOn hs hr).comp
    (continuous_const.sub continuous_id).continuousOn
  intro v hv
  constructor <;> dsimp <;> linarith [hv.1, hv.2]

/-- Lower survival rounding gives upper actual real cost whenever its guard holds. -/
lemma gammaSurvivalQuantile_upper_cost {x v : ℝ} (hx : 0 ≤ x)
    (hv : 0 < v) (hvs : v ≤ gammaSurvival shape rate x) :
    x ≤ gammaSurvivalQuantile hs hr v := by
  have hS := gammaSurvival_mem hs hr hx
  have h := gammaSurvivalQuantile_antitoneOn hs hr ⟨hv, hvs.trans hS.2⟩ hS hvs
  simpa only [gammaSurvivalQuantile_inverse hs hr hx] using h

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SurvivalRank
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {shape rate : ℝ}

lemma gammaSurvival_nonneg (x : ℝ) : 0 ≤ gammaSurvival shape rate x := by
  exact sub_nonneg.mpr (cdf_le_one (gammaMeasure shape rate) x)

lemma gammaSurvival_measurable (hs : 0 < shape) (hr : 0 < rate) :
    Measurable (gammaSurvival shape rate) :=
  measurable_const.sub (gamma_cdf_continuous hs hr).measurable

lemma gammaSurvival_lt_iff (hs : 0 < shape) (hr : 0 < rate)
    {x u : ℝ} (hx : 0 ≤ x) (hu : 0 < u) (hu1 : u ≤ 1) :
    gammaSurvival shape rate x < u ↔ gammaSurvivalQuantile hs hr u < x := by
  have hq := gammaQuantileReal_spec hs hr (show 0 ≤ 1-u by linarith)
    (show 1-u < 1 by linarith)
  change gammaSurvival shape rate x < u ↔
    gammaQuantileReal shape rate hs hr (1-u) < x
  constructor
  · intro h
    apply lt_of_not_ge
    intro hn
    have hc := monotone_cdf (gammaMeasure shape rate) hn
    rw [hq.2] at hc
    dsimp [gammaSurvival] at h
    linarith
  · intro h
    have hc := gamma_cdf_strictMonoOn hs hr hq.1 hx h
    rw [hq.2] at hc
    dsimp [gammaSurvival]
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : PlanarFPP.Edge → Ω → ℝ}

namespace GammaEnvironment

/-- Native Gamma strict positivity transfers through the actual edge marginal. -/
lemma edge_ae_pos (h : GammaEnvironment shape rate P τ) (e : PlanarFPP.Edge) :
    ∀ᵐ ω ∂P, 0 < τ e ω := by
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact gamma_ae_pos shape rate
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

lemma edge_tail_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge) (r : ℝ) :
    P.real {ω | r < τ e ω} = gammaSurvival shape rate r := by
  let := h.probability
  let := isProbabilityMeasure_gammaMeasure hs hr
  have hm : P {ω | τ e ω ≤ r} = gammaMeasure shape rate (Iic r) := by
    rw [← h.marginal e, Measure.map_apply (h.measurable e) measurableSet_Iic]
    rfl
  have hc : P.real {ω | τ e ω ≤ r} = cdf (gammaMeasure shape rate) r := by
    rw [measureReal_def, hm, cdf_eq_real, measureReal_def]
  have he : {ω | r < τ e ω} = {ω | τ e ω ≤ r}ᶜ := by
    ext ω
    simp
  rw [he, measureReal_compl (measurableSet_le (h.measurable e) measurable_const), hc]
  simp [gammaSurvival]

/-- Strict uniform CDF on the closed parameter interval, proved from actual tails. -/
theorem survival_lt_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    P.real {ω | gammaSurvival shape rate (τ e ω) < u} = u := by
  by_cases hz : u = 0
  · subst u
    have he : {ω | gammaSurvival shape rate (τ e ω) < 0} = ∅ := by
      ext ω
      simp [not_lt.mpr (gammaSurvival_nonneg (shape := shape) (rate := rate) (τ e ω))]
    rw [he]
    simp
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have he : {ω | gammaSurvival shape rate (τ e ω) < u} =ᵐ[P]
        {ω | gammaSurvivalQuantile hs hr u < τ e ω} := by
      filter_upwards [h.edge_ae_pos e] with ω hω
      exact propext (gammaSurvival_lt_iff hs hr hω.le hup hu1)
    rw [measureReal_congr he, h.edge_tail_real hs hr]
    have hq := gammaQuantileReal_spec hs hr (show 0 ≤ 1-u by linarith)
      (show 1-u < 1 by linarith)
    dsimp [gammaSurvival, gammaSurvivalQuantile]
    rw [hq.2]
    ring

theorem survival_bin_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    P.real {ω | a ≤ gammaSurvival shape rate (τ e ω) ∧
      gammaSurvival shape rate (τ e ω) < b} = b-a := by
  let := h.probability
  let A : Set Ω := {ω | gammaSurvival shape rate (τ e ω) < a}
  let B : Set Ω := {ω | gammaSurvival shape rate (τ e ω) < b}
  have hA : MeasurableSet A := measurableSet_lt
    ((gammaSurvival_measurable hs hr).comp (h.measurable e)) measurable_const
  have hAB : A ⊆ B := fun ω hω => lt_of_lt_of_le hω hab
  have he : {ω | a ≤ gammaSurvival shape rate (τ e ω) ∧
      gammaSurvival shape rate (τ e ω) < b} = B \ A := by
    ext ω
    simp only [mem_ofPred_eq, mem_sdiff, A, B, not_lt]
    tauto
  rw [he, measureReal_sdiff hAB hA]
  exact congrArg₂ (·-·) (h.survival_lt_real hs hr e b (ha.trans hab) hb)
    (h.survival_lt_real hs hr e a ha (hab.trans hb))

/-- Exact floor-rank law; validity does not require pointwise positive weights. -/
theorem survival_rank_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge)
    (m i : ℕ) (hm : 0 < m) (hi : i < m) :
    P.real {ω | ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i} = 1/(m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : {ω | ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i} =
      {ω | (i : ℝ)/m ≤ gammaSurvival shape rate (τ e ω) ∧
        gammaSurvival shape rate (τ e ω) < ((i : ℝ)+1)/m} := by
    ext ω
    have hp := gammaSurvival_nonneg (shape := shape) (rate := rate) (τ e ω)
    rw [mem_ofPred_eq, mem_ofPred_eq, Nat.floor_eq_iff (by positivity)]
    rw [div_le_iff₀ hm', lt_div_iff₀ hm']
    simp only [mul_comm]
  have hu : ((i : ℝ)+1)/m ≤ 1 := by
    rw [div_le_iff₀ hm']
    have hi' : (i : ℝ)+1 ≤ m := by exact_mod_cast (show i+1 ≤ m by omega)
    simpa using hi'
  rw [he, h.survival_bin_real hs hr e ((i : ℝ)/m) (((i : ℝ)+1)/m)
    (by positivity) (div_le_div_of_nonneg_right (by linarith) hm'.le) hu]
  ring

/-- Finite joint law from actual `iIndepFun`, including the empty edge set. -/
theorem survival_ranks_joint_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset PlanarFPP.Edge)
    (m : ℕ) (hm : 0 < m) (i : PlanarFPP.Edge → ℕ) (hi : ∀ e ∈ S, i e < m) :
    P.real {ω | ∀ e ∈ S, ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i e} =
      (1/(m : ℝ))^S.card := by
  let A : PlanarFPP.Edge → Set ℝ := fun e =>
    {x | ⌊(m : ℝ) * gammaSurvival shape rate x⌋₊ = i e}
  have hA : ∀ e ∈ S, MeasurableSet (A e) := by
    intro e _
    apply measurableSet_eq_fun _ measurable_const
    exact (measurable_const.mul (gammaSurvival_measurable hs hr)).nat_floor
  have hj := h.independent.measure_inter_preimage_eq_mul S (sets := A) hA
  have he : {ω | ∀ e ∈ S, ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i e} =
      ⋂ e ∈ S, τ e ⁻¹' A e := by
    ext ω
    simp [A]
  rw [he, measureReal_def, hj, ENNReal.toReal_prod]
  change (∏ e ∈ S, P.real {ω | ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i e}) = _
  calc
    _ = ∏ _e ∈ S, (1/(m : ℝ)) := by
      apply Finset.prod_congr rfl
      intro e he
      exact h.survival_rank_real hs hr e m (i e) hm (hi e he)
    _ = _ := by simp

end GammaEnvironment
end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKBitLaw
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Finset Filter PlanarFPP
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

lemma measurableSet_gammaDyadicRankCell (hs : 0 < shape) (hr : 0 < rate) (hτ : ∀ e, Measurable (τ e))
    (S : Finset Edge) (t : ℕ) (x : Finset (Edge × Fin t)) :
    MeasurableSet (gammaDyadicRankCell shape rate τ S t x) := by
  simp only [gammaDyadicRankCell,ofPred_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro _
  apply measurableSet_eq_fun _ measurable_const
  exact (measurable_const.mul ((gammaSurvival_measurable hs hr).comp (hτ e))).nat_floor

omit [MeasurableSpace Ω] in
lemma gammaDyadicRankCell_disjoint (τ : Edge → Ω → ℝ) (S : Finset Edge) (t : ℕ)
    {x y : Finset (Edge × Fin t)} (hx : x ⊆ S ×ˢ Finset.univ) (hy : y ⊆ S ×ˢ Finset.univ) (hxy : x ≠ y) :
    Disjoint (gammaDyadicRankCell shape rate τ S t x) (gammaDyadicRankCell shape rate τ S t y) := by
  apply Set.disjoint_left.mpr
  intro ω hωx hωy
  apply hxy
  exact dyadicRanks_injective S t hx hy (fun e he => (hωx e he).symm.trans (hωy e he))

lemma GammaEnvironment.gammaDyadicRankCell_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (x : Finset (Edge × Fin t)) :
    P.real (gammaDyadicRankCell shape rate τ S t x) = 1/(2:ℝ)^((S ×ˢ (Finset.univ : Finset (Fin t))).card) := by
  have hh := h.survival_ranks_joint_real hs hr S (2^t) (by positivity) (dyadicRank t x)
    (fun e _ => dyadicRank_lt t x e)
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  change P.real (gammaDyadicRankCell shape rate τ S t x) = _ at hh
  rw [hh,one_div_pow,← pow_mul,card_product,card_univ,Fintype.card_fin]
  rw [Nat.mul_comm]

/-- Uniform bit-cube probabilities, obtained from the actual Gamma
edge law through an exact disjoint partition into dyadic rank cells. -/
theorem GammaEnvironment.gammaDyadicRankCells_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (A : Finset (Finset (Edge × Fin t)))
    (hA : A ⊆ (S ×ˢ Finset.univ).powerset) :
    P.real (⋃ x ∈ A, gammaDyadicRankCell shape rate τ S t x) = fairFamilyMass (S ×ˢ Finset.univ) A := by
  classical
  let _ := h.probability
  have hd : Set.PairwiseDisjoint (↑A : Set (Finset (Edge × Fin t))) (gammaDyadicRankCell shape rate τ S t) := by
    intro x hx y hy hxy
    exact gammaDyadicRankCell_disjoint τ S t (mem_powerset.mp (hA hx)) (mem_powerset.mp (hA hy)) hxy
  have he := measure_biUnion_finset (μ := P) hd (fun x _ => measurableSet_gammaDyadicRankCell hs hr h.measurable S t x)
  have hreal := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at hreal
  change P.real (⋃ x ∈ A, gammaDyadicRankCell shape rate τ S t x) = ∑ x ∈ A, P.real (gammaDyadicRankCell shape rate τ S t x) at hreal
  rw [hreal]
  simp only [h.gammaDyadicRankCell_real hs hr,sum_const,nsmul_eq_mul,fairFamilyMass,div_eq_mul_inv,one_mul]

/-- Every original environment lies in one of the bit cells almost surely.
Coverage follows from exact mass one, so no choice of a binary expansion on
null endpoint configurations is needed. -/
theorem GammaEnvironment.ae_gammaDyadicRankCell (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) :
    ∀ᵐ ω ∂P, ∃ x ∈ (S ×ˢ (Finset.univ : Finset (Fin t))).powerset, ω ∈ gammaDyadicRankCell shape rate τ S t x := by
  let _ := h.probability
  let U : Set Ω := ⋃ x ∈ (S ×ˢ (Finset.univ : Finset (Fin t))).powerset, gammaDyadicRankCell shape rate τ S t x
  have hm : MeasurableSet U := MeasurableSet.biUnion (Finset.countable_toSet _)
    (fun x _ => measurableSet_gammaDyadicRankCell hs hr h.measurable S t x)
  have hp : P.real U = 1 := by
    rw [h.gammaDyadicRankCells_real hs hr S t _ (Finset.Subset.rfl),fairFamilyMass_powerset]
  have hP : P U = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
    change P.real U = (1 : ℝ≥0∞).toReal
    simpa using hp
  have hz : P (Uᶜ) = 0 := by
    rw [measure_compl hm (measure_ne_top _ _),hP]
    simp
  have hh : ∀ᵐ ω ∂P, ω ∈ U := by
    rw [ae_iff]
    exact hz
  filter_upwards [hh] with ω hω
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hx,hcell⟩ := Set.mem_iUnion.mp hx
  exact ⟨x,hx,hcell⟩

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKForcing
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

lemma ForcesBits.positive_certificate {s : Finset α} {A : Finset (Finset α)}
    {x c : Finset α} (hxs : x ⊆ s) (h : ForcesBits s A x c) : x ∩ c ∈ A := by
  apply h (x ∩ c) ((inter_subset_left).trans hxs)
  intro e he
  simp [he]

theorem forcing_certificates_mem (s : Finset α) (As : List (Finset (Finset α)))
    (cs : List (Finset α)) (x : Finset α) (hxs : x ⊆ s)
    (hforce : List.Forall₂ (fun c A => ForcesBits s A x c) cs As)
    (hdis : cs.Pairwise Disjoint) : x ∈ iteratedDisjointOccurrence s As := by
  apply certificates_mem_iterated s As (cs.map (fun c => x ∩ c)) x hxs
  · clear hdis
    induction hforce with
    | nil => exact List.Forall₂.nil
    | cons h ht ih => exact List.Forall₂.cons (h.positive_certificate hxs) ih
  · rw [List.pairwise_map]
    exact hdis.imp (fun hab => hab.mono (inter_subset_right) (inter_subset_right))
  · intro w hw
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hw
    exact inter_subset_left

theorem finite_fair_BK_forcing (s : Finset α) (As : List (Finset (Finset α)))
    (D : Finset (Finset α)) (hAs : ∀ A ∈ As, UpwardFamily s A)
    (hD : ∀ x ∈ D, x ⊆ s ∧ ∃ cs : List (Finset α),
      List.Forall₂ (fun c A => ForcesBits s A x c) cs As ∧ cs.Pairwise Disjoint) :
    fairFamilyMass s D ≤ (As.map (fairFamilyMass s)).prod := by
  apply (fairFamilyMass_mono s ?_).trans (finite_fair_BK_repeated s As hAs)
  intro x hx
  obtain ⟨hxs,cs,hforce,hdis⟩ := hD x hx
  exact forcing_certificates_mem s As cs x hxs hforce hdis

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridIndependence
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint independence for finite families of tests on disjoint edge sets. -/
namespace GammaFPP.Grid
open PlanarFPP MeasureTheory ProbabilityTheory Set Finset

theorem measurable_extendEdgeWeights (S : Finset Edge) : Measurable (extendEdgeWeights S) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ S
  · simpa only [extendEdgeWeights,dite_eq_left he] using (measurable_pi_apply (⟨e,he⟩ : S))
  · simp only [extendEdgeWeights,dite_eq_right he]
    exact measurable_const

theorem DependsOnEdges.restriction_iff {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    extendEdgeWeights S (fun e : S => w e) ∈ A ↔ w ∈ A := by
  apply hA
  intro e he
  simp [extendEdgeWeights,he]

theorem DependsOnEdges.compl {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) : DependsOnEdges Aᶜ S := by
  intro w w' hh
  exact not_congr (hA w w' hh)

theorem dependsOnEdges_biInter {ι : Type*} (t : Finset ι)
    (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, DependsOnEdges (A i) (S i)) :
    DependsOnEdges (⋂ i ∈ t, A i) (t.biUnion S) := by
  classical
  intro w w' hh
  simp only [mem_iInter]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact hA i hi w w' (fun e he => hh e (mem_biUnion.mpr ⟨i,hi,he⟩))

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem disjoint_edge_events_independent (h : GammaEnvironment shape rate P τ)
    (A B : Set (Edge → ℝ)) (S T : Finset Edge)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : DependsOnEdges A S) (hBT : DependsOnEdges B T) (hST : Disjoint S T) :
    IndepSet {ω | (fun e => τ e ω) ∈ A} {ω | (fun e => τ e ω) ∈ B} P := by
  let _ := h.probability
  have hf := h.independent.indepFun_finset S T hST h.measurable
  have hs : Measurable (fun ω (e : S) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have ht : Measurable (fun ω (e : T) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have hi := (indepFun_iff_indepSet_preimage hs ht).mp hf
    ((extendEdgeWeights S) ⁻¹' A) ((extendEdgeWeights T) ⁻¹' B)
    (hA.preimage (measurable_extendEdgeWeights S)) (hB.preimage (measurable_extendEdgeWeights T))
  have heA : (fun ω (e : S) => τ e ω) ⁻¹' ((extendEdgeWeights S) ⁻¹' A) =
      {ω | (fun e => τ e ω) ∈ A} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hAS.restriction_iff (fun e => τ e ω)
  have heB : (fun ω (e : T) => τ e ω) ⁻¹' ((extendEdgeWeights T) ⁻¹' B) =
      {ω | (fun e => τ e ω) ∈ B} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hBT.restriction_iff (fun e => τ e ω)
  simpa only [heA,heB] using hi

theorem disjoint_edge_events_inter_probability (h : GammaEnvironment shape rate P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j))) :
    P {ω | ∀ i ∈ t, (fun e => τ e ω) ∈ A i} =
      ∏ i ∈ t, P {ω | (fun e => τ e ω) ∈ A i} := by
  classical
  let _ := h.probability
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hAt : ∀ i ∈ t, MeasurableSet (A i) := fun i hi => hA i (mem_insert_of_mem hi)
    have hSt : ∀ i ∈ t, DependsOnEdges (A i) (S i) := fun i hi => hAS i (mem_insert_of_mem hi)
    have hd : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)) := by
      intro i hi j hj hij
      exact hdis (mem_insert_of_mem hi) (mem_insert_of_mem hj) hij
    have hdunion : Disjoint (S a) (t.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hi) (by intro he; exact ha (he ▸ hi))
    have hm : MeasurableSet (⋂ i ∈ t, A i) := MeasurableSet.biInter (t.countable_toSet) hAt
    have hi := disjoint_edge_events_independent h (A a) (⋂ i ∈ t, A i) (S a) (t.biUnion S)
      (hA a (mem_insert_self _ _)) hm (hAS a (mem_insert_self _ _))
      (dependsOnEdges_biInter t A S hSt) hdunion
    have hprob := hi.measure_inter_eq_mul
    have he : {ω | ∀ i ∈ insert a t, (fun e => τ e ω) ∈ A i} =
        {ω | (fun e => τ e ω) ∈ A a} ∩ {ω | (fun e => τ e ω) ∈ ⋂ i ∈ t, A i} := by
      ext ω; simp
    rw [he,hprob,Finset.prod_insert ha]
    congr 1
    simpa only [mem_iInter] using ih hAt hSt hd

/-- The amplification step in cr:rare-fast: M disjoint trials with individual
success probability at least p have joint failure probability at most (1-p)^M. -/
theorem disjoint_trials_failure_bound (h : GammaEnvironment shape rate P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)))
    (p : ℝ)
    (hprob : ∀ i ∈ t, p ≤ P.real {ω | (fun e => τ e ω) ∈ A i}) :
    P.real {ω | ∀ i ∈ t, (fun e => τ e ω) ∉ A i} ≤ (1-p)^t.card := by
  classical
  let _ := h.probability
  have he := disjoint_edge_events_inter_probability h t (fun i => (A i)ᶜ) S
    (fun i hi => (hA i hi).compl) (fun i hi => (hAS i hi).compl) hdis
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_prod] at her
  change P.real _ = ∏ i ∈ t, P.real {ω | (fun e => τ e ω) ∉ A i} at her
  simp only [mem_compl_iff] at her
  rw [her]
  calc
    _ ≤ ∏ _i ∈ t, (1-p) := by
      apply Finset.prod_le_prod
      · intro i _; exact measureReal_nonneg
      · intro i hi
        have hm := (hA i hi).preimage (Measurable.of_eval h.measurable)
        have hc := measureReal_compl (μ := P) hm
        simp only [Set.preimage] at hc
        change P.real ({ω | (fun e => τ e ω) ∈ A i}ᶜ) ≤ _
        rw [hc]
        simpa using sub_le_sub_left (hprob i hi) 1
    _ = _ := by simp

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Stationarity
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {ν : Measure ℝ}

/-- Every measurable configuration observable has translation-invariant law. -/
theorem IidEnvironment.translated_event_probability
    (h : IidEnvironment ν P τ) (a : Vertex)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) :
    P {ω | (fun e => τ (shiftEdge a e) ω) ∈ A} =
      P {ω | (fun e => τ e ω) ∈ A} := by
  have he := congrArg (fun Q : Measure (Edge → ℝ) => Q A)
    ((h.translate a).jointLaw.trans h.jointLaw.symm)
  rw [Measure.map_apply (Measurable.of_eval (fun e => h.measurable _)) hA,
    Measure.map_apply (Measurable.of_eval h.measurable) hA] at he
  exact he

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MGF
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Exponential weighting changes the Gamma rate from `rate` to `rate - theta`. -/
lemma gamma_weighted_density {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal (exp (theta * x)) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) *
        gammaPDF shape (rate - theta) x := by
  have hs : 0 < rate - theta := sub_pos.mpr htheta
  have hc : 0 ≤ (rate / (rate - theta)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hrate hs) shape).le
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc]
    congr 1
    have hexp : exp (-(rate * x)) * exp (theta * x) =
        exp (-((rate - theta) * x)) := by
      rw [← exp_add]
      congr 1
      ring
    calc
      rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x)) *
          exp (theta * x) =
          rate ^ shape / Gamma shape * x ^ (shape - 1) *
            (exp (-(rate * x)) * exp (theta * x)) := by ring
      _ = rate ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x)) := by rw [hexp]
      _ = (rate / (rate - theta)) ^ shape *
          ((rate - theta) ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x))) := by
        rw [Real.div_rpow hrate.le hs.le]
        have hpow : (rate - theta) ^ shape ≠ 0 :=
          (Real.rpow_pos_of_pos hs shape).ne'
        have hgamma : Gamma shape ≠ 0 := (Real.Gamma_pos_of_pos hshape).ne'
        field_simp [hpow, hgamma]
  · rw [gammaPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- The nonnegative exponential moment from the normalized density with shifted rate. -/
theorem gamma_lintegral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x)) ∂gammaMeasure shape rate) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x))
    ∂volume.withDensity (gammaPDF shape rate)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, gamma_weighted_density hshape hrate htheta]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one hshape (sub_pos.mpr htheta), mul_one]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

lemma IidEnvironment.measurable_edgeSum (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) : Measurable (edgeSum S τ) :=
  Finset.measurable_sum S (fun e _ => h.measurable e)

variable {shape rate theta : ℝ}

/-- The nonnegative exponential moment of a finite iid Gamma edge sum. -/
theorem GammaEnvironment.lintegral_exp_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) =
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card := by
  classical
  let X : PlanarFPP.Edge → Ω → ℝ≥0∞ :=
    fun e ω => ENNReal.ofReal (Real.exp (theta * τ e ω))
  have hX : ∀ e, Measurable (X e) := by
    intro e
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable e)))
  have hXi : iIndepFun X P := h.independent.comp
    (fun _ (x : ℝ) => ENNReal.ofReal (Real.exp (theta * x))) (fun _ => by fun_prop)
  have hpoint (ω : Ω) : ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) =
      ∏ e ∈ S, X e ω := by
    rw [edgeSum, Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun e _ => (Real.exp_pos _).le)
  have hm (e : PlanarFPP.Edge) :
      (∫⁻ ω, X e ω ∂P) = ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
    change (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * τ e ω)) ∂P) = _
    rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (Real.exp (theta * x)))
      (by fun_prop) (h.measurable e), h.marginal e]
    exact gamma_lintegral_exp hshape hrate htheta
  simp_rw [hpoint]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun S X hXi hX]
  simp only [hm, Finset.prod_const]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate theta : ℝ}

/-- Exponential Markov bound for a real parameter `theta` and an arbitrary real threshold. -/
theorem GammaEnvironment.exponential_markov_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  have hm : Measurable (fun ω => ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable_edgeSum S)))
  calc
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
        P {ω | ENNReal.ofReal (Real.exp (theta * a)) ≤
          ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) /
        ENNReal.ofReal (Real.exp (theta * a)) :=
      meas_ge_le_lintegral_div hm.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ = _ := by rw [h.lintegral_exp_edgeSum hshape hrate htheta S]

/-- Gamma Chernoff upper-tail estimate for `0 < theta < rate`. -/
theorem GammaEnvironment.upper_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_pos : 0 < theta) (htheta : theta < rate)
    (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | a ≤ edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate htheta S a)
  intro ω hω
  exact mul_le_mul_of_nonneg_left hω htheta_pos.le

/-- Gamma Chernoff lower-tail estimate for `theta < 0`. -/
theorem GammaEnvironment.lower_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_neg : theta < 0) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | edgeSum S τ ω ≤ a} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate (htheta_neg.trans hrate) S a)
  intro ω hω
  exact mul_le_mul_of_nonpos_left hω htheta_neg.le

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPath
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

lemma trace_edge_length (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).length = ds.length := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simpa only [trace, List.map_cons, List.length_cons] using
      (congrArg Nat.succ (ih (p + d.delta)))

lemma pathCost_trace_edge_sum (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p ds = (((trace p ds).map traversalEdge).map w).sum := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp only [pathCost, trace, List.map_cons, List.sum_cons,
      traversalEdge, ih]

/-- Only a trail's traversal sum can be replaced by its distinct-edge set sum. -/
lemma pathCost_eq_distinct_edgeSum (w : Edge → ℝ) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) :
    pathCost w p ds = ∑ e ∈ ((trace p ds).map traversalEdge).toFinset, w e := by
  classical
  rw [pathCost_trace_edge_sum]
  exact (List.sum_toFinset w hn).symm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Genuine Gamma lower tail for any fixed trail, with arbitrary real threshold.
The positive parameter s uses the native MGF at theta=-s. -/
theorem GammaEnvironment.cheap_path_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) (t : ℝ) :
    P {ω | pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ ds.length /
        ENNReal.ofReal (Real.exp (-s * t)) := by
  classical
  have hc : ((trace p ds).map traversalEdge).toFinset.card = ds.length := by
    rw [List.toFinset_card_of_nodup hn, trace_edge_length]
  have he (ω : Ω) : edgeSum ((trace p ds).map traversalEdge).toFinset τ ω =
      pathCost (fun e => τ e ω) p ds := by
    exact (pathCost_eq_distinct_edgeSum (fun e => τ e ω) p ds hn).symm
  have hb := h.lower_tail_edgeSum hs hr (neg_neg_of_pos hsp)
    ((trace p ds).map traversalEdge).toFinset t
  simpa only [he, hc, sub_neg_eq_add] using hb

/-- The probability that a finite family contains a cheap trail is bounded by
its cardinality times the single-trail estimate. -/
theorem GammaEnvironment.cheap_path_family_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (F : Finset (List Step)) (n : ℕ)
    (hF : ∀ ds ∈ F, ((trace p ds).map traversalEdge).Nodup ∧ ds.length = n)
    (t : ℝ) :
    P {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (F.card : ℝ≥0∞) * ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
  classical
  have he : {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} =
      ⋃ ds ∈ F, {ω | pathCost (fun e => τ e ω) p ds ≤ t} := by
    ext ω
    simp
  rw [he]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _ds ∈ F, ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
      apply Finset.sum_le_sum
      intro ds hds
      simpa only [(hF ds hds).2] using
        h.cheap_path_probability hs hr s hsp p ds (hF ds hds).1 t
    _ = _ := by simp

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathCounting
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

attribute [local instance] OAI.GammaFPP.cheapStepFintype
private lemma cheapStep_card : Fintype.card Step = 4 := by decide

lemma card_fixedStepLists_le (n : ℕ) : (fixedStepLists n).card ≤ 4 ^ n := by
  classical
  calc
    (fixedStepLists n).card ≤ (Finset.univ : Finset (Fin n → Step)).card :=
      Finset.card_image_le
    _ = 4 ^ n := by rw [Finset.card_univ, Fintype.card_fun, cheapStep_card, Fintype.card_fin]

lemma card_fixedTrailLists_le (p : Vertex) (n : ℕ) :
    (fixedTrailLists p n).card ≤ 4 ^ n := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_fixedStepLists_le n)

/-- Exact event equality; there is no hidden restriction to a selected optimizer. -/
lemma fixedTrail_event_eq {Ω : Type*} (τ : Edge → Ω → ℝ)
    (p : Vertex) (n : ℕ) (t : ℝ) :
    {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} =
    {ω | ∃ ds ∈ fixedTrailLists p n, pathCost (fun e => τ e ω) p ds ≤ t} := by
  ext ω
  simp only [Set.mem_ofPred_eq, mem_fixedTrailLists]
  constructor
  · rintro ⟨ds, hl, hn, hc⟩
    exact ⟨ds, ⟨hl, hn⟩, hc⟩
  · rintro ⟨ds, ⟨hl, hn⟩, hc⟩
    exact ⟨ds, hl, hn, hc⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual fixed-length trails, with a proved four-way exponential count. -/
theorem GammaEnvironment.cheap_fixed_length_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (n : ℕ) (t : ℝ) :
    P {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} ≤
      ((4 ^ n : ℕ) : ℝ≥0∞) *
        ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
          ENNReal.ofReal (Real.exp (-s * t))) := by
  rw [fixedTrail_event_eq]
  have hb := h.cheap_path_family_probability hs hr s hsp p (fixedTrailLists p n) n
    (fun ds hds => ((mem_fixedTrailLists p n ds).mp hds).symm) t
  refine hb.trans (mul_le_mul_left ?_ _)
  exact_mod_cast card_fixedTrailLists_le p n

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathDecay
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP
open scoped ENNReal

lemma cheapChernoff_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapChernoff shape rate := by
  have hl : 0 < Real.log (16 : ℝ) := Real.log_pos (by norm_num)
  exact mul_pos hr (sub_pos.mpr (Real.one_lt_exp_iff.mpr (div_pos hl hs)))

lemma cheapSlope_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapSlope shape rate :=
  div_pos (Real.log_pos (by norm_num)) (cheapChernoff_pos hs hr)

/-- The exact native Gamma Laplace factor is 1/16 at the chosen parameter. -/
lemma cheapChernoff_factor {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    (rate / (rate + cheapChernoff shape rate)) ^ shape = (1 / 16 : ℝ) := by
  have hd : rate + cheapChernoff shape rate =
      rate * Real.exp (Real.log 16 / shape) := by
    unfold cheapChernoff
    ring
  have hratio : rate / (rate + cheapChernoff shape rate) =
      Real.exp (-(Real.log 16 / shape)) := by
    rw [hd, Real.exp_neg]
    field_simp [hr.ne', Real.exp_ne_zero]
  rw [hratio, ← Real.exp_mul]
  have he : -(Real.log 16 / shape) * shape = -Real.log 16 := by
    field_simp [hs.ne']
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  norm_num

lemma cheapChernoff_mul_slope {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    cheapChernoff shape rate * cheapSlope shape rate = Real.log 2 := by
  unfold cheapSlope
  field_simp [(cheapChernoff_pos hs hr).ne']

/-- Exact cancellation of counting, Laplace factor and linear threshold. -/
lemma cheap_count_bound_eq {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) (n : ℕ) :
    (4 : ℝ)^n * (((rate / (rate + cheapChernoff shape rate)) ^ shape)^n /
      Real.exp (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) =
        (1 / 2 : ℝ)^n := by
  rw [cheapChernoff_factor hs hr]
  have he : -cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)) =
      (n : ℝ) * (-Real.log 2) := by
    have hc := cheapChernoff_mul_slope hs hr
    calc
      _ = -(cheapChernoff shape rate * cheapSlope shape rate) * (n : ℝ) := by ring
      _ = _ := by rw [hc]; ring
  rw [he, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← div_pow, ← mul_pow]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual trails of n steps from p are exponentially unlikely to cost at
most c*n. This includes n=0, where the empty path has probability one. -/
theorem GammaEnvironment.cheap_fixed_length_decay_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (n : ℕ) :
    P.real {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧
        pathCost (fun e => τ e ω) p ds ≤ cheapSlope shape rate * (n : ℝ)} ≤
      (1 / 2 : ℝ)^n := by
  have hsp := cheapChernoff_pos hs hr
  have hbase : 0 ≤ (rate / (rate + cheapChernoff shape rate)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hr (add_pos hr hsp)) shape).le
  have hden : ENNReal.ofReal (Real.exp
      (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfin : ((4 ^ n : ℕ) : ℝ≥0∞) *
      ((ENNReal.ofReal ((rate / (rate + cheapChernoff shape rate)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp
          (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ))))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp)
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden)
  have hb := ENNReal.toReal_mono hfin
    (h.cheap_fixed_length_probability hs hr (cheapChernoff shape rate) hsp p n
      (cheapSlope shape rate * (n : ℝ)))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Nat.cast_pow, Nat.cast_ofNat] at hb
  change P.real _ ≤ _ at hb
  rw [cheap_count_bound_eq hs hr n] at hb
  exact hb

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapLongTrails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Exponential decay is summable, including the nonempty bad event at n=0. -/
theorem GammaEnvironment.summable_cheapTrailEvent_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) : Summable (fun n => P.real (cheapTrailEvent shape rate τ p n)) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact hg.of_nonneg_of_le (fun _ => measureReal_nonneg)
    (fun n => h.cheap_fixed_length_decay_real hs hr p n)

/-- At each fixed start, almost surely all sufficiently long trails have
strictly positive linear cost. No independence across lengths is used. -/
theorem GammaEnvironment.ae_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  let := h.probability
  have hsum : (∑' n, P (cheapTrailEvent shape rate τ p n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      (h.summable_cheapTrailEvent_real hs hr p).tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, ?_⟩
  intro ds hlen htrail
  by_contra hc
  exact hN ds.length hlen ⟨ds, rfl, htrail, le_of_not_gt hc⟩

/-- Countably many lattice starts may share one event; the length cutoff can
depend on both the environment and the start. -/
theorem GammaEnvironment.ae_all_starts_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  rw [ae_all_iff]
  intro p
  exact h.ae_long_trails_cost hs hr p

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PassageLowerBound
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Filter

/-- Each original nearest-neighbor step contributes at most one L1 unit. -/
lemma displacement_natAbs_sum_le_length (ds : List Step) :
    (displacement ds).1.natAbs + (displacement ds).2.natAbs ≤ ds.length := by
  induction ds with
  | nil => simp [displacement]
  | cons d ds ih =>
      have h₁ := Int.natAbs_add_le d.delta.1 (displacement ds).1
      have h₂ := Int.natAbs_add_le d.delta.2 (displacement ds).2
      have hd : d.delta.1.natAbs + d.delta.2.natAbs = 1 := by
        cases d <;> norm_num [Step.delta]
      simp only [displacement_cons, List.length_cons]
      change (d.delta.1 + (displacement ds).1).natAbs +
        (d.delta.2 + (displacement ds).2).natAbs ≤ ds.length + 1
      omega

/-- Literal latticeDistance, not the product max norm. -/
lemma latticeDistance_endpoint_le_length (p : Vertex) (ds : List Step) :
    latticeDistance p (p + displacement ds) ≤ ds.length := by
  simpa only [latticeDistance, Prod.fst_add, Prod.snd_add, add_sub_cancel_left] using
    displacement_natAbs_sum_le_length ds

/-- Erasure preserves the endpoint, so every sufficiently distant arbitrary
path inherits the long-trail lower bound, even if it repeats edges. -/
lemma pathCost_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) (ds : List Step)
    (hend : p + displacement ds = q) :
    c * (latticeDistance p q : ℝ) < pathCost w p ds := by
  obtain ⟨es, he, hn, hcost⟩ := LoopErase.erase_path_loops w hw p ds
  have hend' : p + displacement es = q := by rw [he, hend]
  have hdist : latticeDistance p q ≤ es.length := by
    simpa only [hend'] using latticeDistance_endpoint_le_length p es
  have hdistR : (latticeDistance p q : ℝ) ≤ (es.length : ℝ) := by
    exact_mod_cast hdist
  exact (mul_le_mul_of_nonneg_left hdistR hc).trans_lt
    ((hN es (hq.trans hdist) hn).trans_le hcost)

/-- Taking the infimum of path costs preserves the non-strict lower bound,
without requiring the existence of a minimizing path. -/
lemma passageTime_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) :
    c * (latticeDistance p q : ℝ) ≤ passageTime w p q := by
  apply le_csInf (path_costs_nonempty w p q)
  rintro t ⟨ds, hend, rfl⟩
  exact (pathCost_lower_of_long_trails w hw c hc p N hN q hq ds hend).le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- On one probability-one event, every lattice start has an eventual metric
lower bound for all distant endpoints. The cutoff may depend on start/sample. -/
theorem GammaEnvironment.ae_all_starts_passageTime_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ q : Vertex,
      N ≤ latticeDistance p q →
        cheapSlope shape rate * (latticeDistance p q : ℝ) ≤
          passageTime (fun e => τ e ω) p q := by
  filter_upwards [h.ae_positive, h.ae_all_starts_long_trails_cost hs hr] with ω hpos hlong
  intro p
  obtain ⟨N, hN⟩ := hlong p
  refine ⟨N, ?_⟩
  intro q hq
  exact passageTime_lower_of_long_trails (fun e => τ e ω) (fun e => (hpos e).le)
    (cheapSlope shape rate) (cheapSlope_pos hs hr).le p N hN q hq

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanPositive
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped Topology ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Fatou needs only eventual lower bounds, not samplewise convergence. -/
lemma lower_le_limit_integral_of_ae_eventually [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (a m : ℝ)
    (hX : ∀ n, Measurable (X n)) (hI : ∀ n, Integrable (X n) P)
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω)
    (hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, a ≤ X n ω)
    (hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 m)) (hm : 0 ≤ m) :
    a ≤ m := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (X n ω)
  have hmeas : ∀ n, Measurable (F n) := fun n => (hX n).ennreal_ofReal
  have hpoint : ∀ᵐ ω ∂P, ENNReal.ofReal a ≤ liminf (fun n => F n ω) atTop := by
    filter_upwards [hlower] with ω hω
    exact le_liminf_of_le (h := hω.mono fun n hn => ENNReal.ofReal_le_ofReal hn)
  have hlow : ENNReal.ofReal a ≤ ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P := by
    simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hpoint
  have hfatou := lintegral_liminf_le (μ := P) (u := atTop) hmeas
  have hint (n : ℕ) : (∫⁻ ω, F n ω ∂P) = ENNReal.ofReal (∫ ω, X n ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hI n) (hpos n)).symm
  have ht : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 (ENNReal.ofReal m)) := by
    simpa only [hint] using ENNReal.tendsto_ofReal hlimit
  have hb : ENNReal.ofReal a ≤ ENNReal.ofReal m := by
    simpa only [ht.liminf_eq] using hlow.trans hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hm).mp hb

/-- Literal lattice L1 distance scales under natural multiplication. -/
lemma latticeDistance_zero_nsmul (z : Vertex) (n : ℕ) :
    latticeDistance 0 (n • z) = n * latticeDistance 0 z := by
  simp [latticeDistance, nsmul_eq_mul, Int.natAbs_mul, Nat.mul_add]

variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The actual Fekete mean limit has the same positive linear lower bound as
the eventual path metric. The zero direction is treated before division. -/
theorem GammaEnvironment.directionalMeanConstant_linear_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ directionalMeanConstant h hs hr z := by
  by_cases hz : z = 0
  · subst z
    simp [latticeDistance, h.directionalMeanConstant_zero hs hr]
  let : IsProbabilityMeasure P := h.probability
  have hd : 0 < latticeDistance 0 z := by
    by_contra hn
    have hd0 : latticeDistance 0 z = 0 := Nat.eq_zero_of_not_pos hn
    have hxy : z.1 = 0 ∧ z.2 = 0 := by simpa [latticeDistance] using hd0
    exact hz (Prod.ext hxy.1 hxy.2)
  let X : ℕ → Ω → ℝ := fun n ω => passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
  have hX : ∀ n, Measurable (X n) := fun n =>
    (h.measurable_passageTime 0 (n • z)).div_const (n : ℝ)
  have hI : ∀ n, Integrable (X n) P := fun n =>
    (h.integrable_passageTime hs hr 0 (n • z)).div_const (n : ℝ)
  have hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω := by
    intro n
    filter_upwards [h.ae_positive] with ω hω
    exact div_nonneg (passageTime_nonneg _ (fun e => (hω e).le) 0 (n • z))
      (Nat.cast_nonneg n)
  have hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ X n ω := by
    filter_upwards [h.ae_all_starts_passageTime_lower hs hr] with ω hω
    obtain ⟨N, hN⟩ := hω 0
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hnd : N ≤ latticeDistance 0 (n • z) := by
      rw [latticeDistance_zero_nsmul]
      nlinarith
    have hb := hN (n • z) hnd
    rw [latticeDistance_zero_nsmul, Nat.cast_mul] at hb
    change cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤
      passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop
      (𝓝 (directionalMeanConstant h hs hr z)) := by
    simpa only [X, integral_div, meanPassageSequence] using h.meanPassageSequence_tendsto hs hr z
  exact lower_le_limit_integral_of_ae_eventually X _ _ hX hI hpos hlower hlimit
    (h.directionalMeanConstant_nonneg hs hr z)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanNorm
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Topology

/-- Positive denominators transport a lattice coercivity bound to rationals. -/
lemma rationalMean_lower (m : Vertex → ℝ) (c : ℝ)
    (hm : ∀ x, c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|) ≤ m x)
    (q : ℚ × ℚ) :
    c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ rationalMean m q := by
  let x := rationalNumerator q
  let n := rationalDenominator q
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (rationalDenominator_pos q)
  have he := rationalLatticePoint_numerator_denominator q
  have h₁ : (x.1 : ℝ) / (n : ℝ) = (q.1 : ℝ) := by
    have hq : (x.1 : ℚ) / (n : ℚ) = q.1 := by
      simpa only [rationalLatticePoint] using congrArg Prod.fst he
    exact_mod_cast hq
  have h₂ : (x.2 : ℝ) / (n : ℝ) = (q.2 : ℝ) := by
    have hq : (x.2 : ℚ) / (n : ℚ) = q.2 := by
      simpa only [rationalLatticePoint] using congrArg Prod.snd he
    exact_mod_cast hq
  change _ ≤ m x / (n : ℝ)
  rw [← h₁, ← h₂, abs_div, abs_div, abs_of_pos hn]
  simpa only [← add_div, ← mul_div_assoc] using
    div_le_div_of_nonneg_right (hm x) hn.le

/-- A closed inequality on the rational image holds on its real closure. -/
lemma realMeanExtension_lower {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (c : ℝ) (hl : ∀ q, c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ f q)
    (v : ℝ × ℝ) : c * (|v.1| + |v.2|) ≤ realMeanExtension f v := by
  apply isClosed_property rationalPairCast_dense
    (p := fun v => c * (|v.1| + |v.2|) ≤ realMeanExtension f v) ?_ ?_ v
  · exact isClosed_le
      (continuous_const.mul (continuous_fst.abs.add continuous_snd.abs))
      (realMeanExtension_uniformContinuous hf).continuous
  · intro q
    rw [realMeanExtension_on_rat hf]
    exact hl q

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma gammaMeanPairSeminorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : ℝ × ℝ) :
    cheapSlope shape rate * (|v.1| + |v.2|) ≤ gammaMeanPairSeminorm h hs hr v := by
  change _ ≤ realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v
  have hlip := rationalMean_l1 (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)
  apply realMeanExtension_lower
    (rational_l1_lipschitz _ ⟨shape/rate, (div_pos hs hr).le⟩ hlip).uniformContinuous
  intro q
  apply rationalMean_lower
  intro z
  simpa [latticeDistance] using h.directionalMeanConstant_linear_lower hs hr z

lemma gammaMeanNorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : Plane) : cheapSlope shape rate * (|v 0| + |v 1|) ≤ gammaMeanNorm h hs hr v :=
  gammaMeanPairSeminorm_lower h hs hr (v 0, v 1)

/-- The real extension of the Gamma directional mean constants is a norm. -/
theorem gammaMeanNorm_laws
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    TimeConstantNorm (gammaMeanNorm h hs hr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    exact apply_nonneg (gammaMeanPairSeminorm h hs hr) (v 0, v 1)
  · intro v
    constructor
    · intro hv
      have hb := gammaMeanNorm_lower h hs hr v
      have hc := cheapSlope_pos hs hr
      rw [hv] at hb
      have h₀ : v 0 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      have h₁ : v 1 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      ext i
      fin_cases i
      · exact h₀
      · exact h₁
    · rintro rfl
      change gammaMeanPairSeminorm h hs hr 0 = 0
      exact map_zero _
  · intro v w
    change gammaMeanPairSeminorm h hs hr ((v 0, v 1) + (w 0, w 1)) ≤ _
    exact map_add_le_add (gammaMeanPairSeminorm h hs hr) _ _
  · intro a v
    change gammaMeanPairSeminorm h hs hr (a • (v 0, v 1)) = _
    simpa only [Real.norm_eq_abs, gammaMeanNorm] using map_smul_eq_mul (gammaMeanPairSeminorm h hs hr) a (v 0, v 1)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RealDirectionGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

theorem plane_coordinate_le_norm (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

theorem plane_norm_le_coordinates (v : Plane) : ‖v‖ ≤ |v 0| + |v 1| := by
  let x : Plane := PiLp.single 2 0 (v 0)
  let y : Plane := PiLp.single 2 1 (v 1)
  have hv : v = x+y := by
    ext i
    fin_cases i <;> simp [x,y]
  have hx : ‖x‖ = |v 0| := by simp [x]
  have hy : ‖y‖ = |v 1| := by simp [y]
  calc
    ‖v‖ = ‖x+y‖ := congrArg norm hv
    _ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    _ = _ := by rw [hx,hy]

theorem latticeDistance_le_norm (p q : Vertex) :
    (latticeDistance p q : ℝ) ≤ 2 * ‖latticeEmbed q - latticeEmbed p‖ := by
  have h0 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 0
  have h1 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 1
  have hc (a : ℤ) : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [latticeDistance, Nat.cast_add, hc, Int.cast_sub]
  simpa only [latticeEmbed, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, two_mul] using add_le_add h0 h1

theorem latticeFloor_error (v : Plane) : ‖latticeEmbed (latticeFloor v) - v‖ ≤ 2 := by
  have hi (i : Fin 2) : |(latticeEmbed (latticeFloor v) - v) i| ≤ 1 := by
    have hle := Int.floor_le (v i)
    have hlt := Int.lt_floor_add_one (v i)
    have he : (latticeEmbed (latticeFloor v) - v) i = (⌊v i⌋ : ℝ) - v i := by
      fin_cases i <;> rfl
    rw [he, abs_of_nonpos (by linarith)]
    linarith
  exact (plane_norm_le_coordinates _).trans (by linarith [hi 0, hi 1])

theorem timeConstantNorm_lipschitz_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v w, |μ v - μ w| ≤ B * ‖v-w‖ := by
  let e0 : Plane := PiLp.single 2 0 1
  let e1 : Plane := PiLp.single 2 1 1
  let B := μ e0 + μ e1 + 1
  have hB : 0 < B := by dsimp [B]; linarith [hμ.nonneg e0, hμ.nonneg e1]
  have hu (v : Plane) : μ v ≤ B * ‖v‖ := by
    have he : v = v 0 • e0 + v 1 • e1 := by
      ext i; fin_cases i <;> simp [e0, e1]
    have ht := hμ.triangle (v 0 • e0) (v 1 • e1)
    rw [← he, hμ.homogeneous, hμ.homogeneous] at ht
    have h0 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 0) (hμ.nonneg e0)
    have h1 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 1) (hμ.nonneg e1)
    dsimp [B]
    nlinarith [norm_nonneg v]
  refine ⟨B, hB, ?_⟩
  intro v w
  apply abs_le.mpr
  have h1 := hμ.triangle (v-w) w
  have h2 := hμ.triangle (w-v) v
  simp only [sub_add_cancel] at h1 h2
  have hu1 := hu (v-w)
  have hu2 := hu (w-v)
  rw [norm_sub_rev] at hu2
  constructor <;> linarith

end GammaFPP.RealDirectionBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CoordinateTails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma coordinateAllowance_pos (hs : 0 < shape) (hr : 0 < rate) :
    0 < coordinateAllowance shape rate := by
  unfold coordinateAllowance
  positivity

/-- Exponential upper tail for the cost of a straight lattice path. -/
theorem GammaEnvironment.costly_straight_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp ((rate / 2) * t)) := by
  have hp : 0 < rate / 2 := by positivity
  have hl : rate / 2 < rate := by linarith
  have he : rate / (rate - rate / 2) = 2 := by
    have hd : rate - rate / 2 ≠ 0 := (sub_pos.mpr hl).ne'
    field_simp [hd]; ring
  have hb := h.upper_tail_edgeSum hs hr hp hl
    ((range n).image (straightEdge p d)) t
  simpa only [edgeSum, pathCost_replicate_edgeSet, he,
    card_image_of_injective _ (straightEdge_injective p d), card_range] using hb

/-- The real-valued upper tail for the cost of a straight lattice path. -/
theorem GammaEnvironment.costly_straight_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      ((2 : ℝ) ^ shape) ^ n * Real.exp (-(rate / 2) * t) := by
  have hbase : 0 ≤ (2 : ℝ) ^ shape := (Real.rpow_pos_of_pos (by norm_num) shape).le
  have hden : ENNReal.ofReal (Real.exp ((rate / 2) * t)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hn : (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ n /
      ENNReal.ofReal (Real.exp ((rate / 2) * t)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden
  have hb := ENNReal.toReal_mono hn (h.costly_straight_probability hs hr p d n t)
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hbase, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hb
  change P.real _ ≤ _ at hb
  rw [show -(rate / 2) * t = -((rate / 2) * t) by ring, Real.exp_neg]
  simpa only [div_eq_mul_inv] using hb

lemma gamma_half_rate_mgf_bound (hs : 0 < shape) :
    (2 : ℝ) ^ shape ≤ Real.exp (shape + 1) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hl : Real.log (2 : ℝ) ≤ 1 := by
    have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hb ⊢
    exact hb
  nlinarith

/-- Exponential tail above the linear allowance, for every real excess `t`. -/
theorem GammaEnvironment.costly_straight_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (n : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      Real.exp (-(rate / 2) * t) := by
  refine (h.costly_straight_probability_real hs hr p d n
    (coordinateAllowance shape rate * n + t)).trans ?_
  have hp : ((2 : ℝ) ^ shape) ^ n ≤ Real.exp ((n : ℝ) * (shape + 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.rpow_pos_of_pos (by norm_num) shape).le
      (gamma_half_rate_mgf_bound hs) n
  calc
    ((2 : ℝ) ^ shape) ^ n *
        Real.exp (-(rate / 2) * (coordinateAllowance shape rate * n + t)) ≤
        Real.exp ((n : ℝ) * (shape + 1)) *
          Real.exp (-(rate / 2) * (coordinateAllowance shape rate * n + t)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-(rate / 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      unfold coordinateAllowance
      field_simp [hr.ne']; ring

theorem GammaEnvironment.costly_horizontal_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (horizontal a)} ≤ Real.exp (-(rate / 2) * t) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_left ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.east a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_right ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.west (-a).toNat t

theorem GammaEnvironment.costly_vertical_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (vertical a)} ≤ Real.exp (-(rate / 2) * t) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_left ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.north a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_right ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.south (-a).toNat t

/-- A union bound for the two coordinate legs, counting every edge traversal. -/
theorem GammaEnvironment.costly_coordinatePath_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ≤
      2 * Real.exp (-(rate / 4) * t) := by
  let := h.probability
  let A := {ω | coordinateAllowance shape rate * ((q.1-p.1).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) p (horizontal (q.1-p.1))}
  let B := {ω | coordinateAllowance shape rate * ((q.2-p.2).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) (p + displacement (horizontal (q.1-p.1)))
      (vertical (q.2-p.2))}
  have hsub : {ω | coordinateAllowance shape rate * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ⊆ A ∪ B := by
    intro ω hω
    change _ ∨ _
    by_contra hn
    push Not at hn
    simp only [Set.mem_ofPred_eq, coordinatePath, pathCost_append, latticeDistance,
      Nat.cast_add] at hω
    simp only [A, B, Set.mem_ofPred_eq, not_le] at hn
    linarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le A B).trans ?_)
  have ha := h.costly_horizontal_excess_probability_real hs hr p (q.1-p.1) (t/2)
  have hb := h.costly_vertical_excess_probability_real hs hr
    (p + displacement (horizontal (q.1-p.1))) (q.2-p.2) (t/2)
  change P.real A + P.real B ≤ _
  change P.real A ≤ _ at ha
  change P.real B ≤ _ at hb
  have he : -(rate / 2) * (t / 2) = -(rate / 4) * t := by ring
  rw [he] at ha hb
  linarith

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialModulus
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory PlanarFPP Finset Filter Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Finite union bound over all ordered pairs, without independence of path events. -/
theorem GammaEnvironment.gammaBadConnections_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (ε : ℝ) (n : ℕ) :
    P.real (gammaBadConnections shape rate τ ε n) ≤
      (2 * (n : ℝ) + 1) ^ 4 * (2 * Real.exp (-(rate / 4) * (ε * n))) := by
  let := h.probability
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _pq ∈ (latticeBox n) ×ˢ (latticeBox n),
        2 * Real.exp (-(rate / 4) * (ε * n)) :=
      sum_le_sum (fun pq _ => h.costly_coordinatePath_probability_real hs hr pq.1 pq.2 (ε * n))
    _ = _ := by simp [latticeBox_card]; ring

/-- The only summability requirement is positive rate times positive epsilon. -/
theorem summable_gamma_box_connection_bound {rate ε : ℝ}
    (hr : 0 < rate) (hε : 0 < ε) :
    Summable (fun n : ℕ =>
      (2 * (n : ℝ) + 1) ^ 4 * (2 * Real.exp (-(rate / 4) * (ε * n)))) := by
  apply (PlanarFPP.summable_box_connection_bound (mul_pos hr hε)).congr
  intro n
  have he : -(rate * ε) * (n : ℝ) / 4 = -(rate / 4) * (ε * n) := by ring
  rw [he]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OriginEscape
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.UniformShapeBridge
open MeasureTheory Filter Set
open scoped Topology

theorem pathCost_take_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (i : ℕ) :
    pathCost w p (ds.take i) ≤ pathCost w p ds := by
  have he := pathCost_append w p (ds.take i) (ds.drop i)
  rw [List.take_append_drop] at he
  have hn := pathCost_nonneg hw (p+displacement (ds.take i)) (ds.drop i)
  linarith

theorem path_confined_of_escape (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (R a : ℝ)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hcost : pathCost w p ds < a) :
    PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  intro i _
  change ‖latticeEmbed (p+displacement (ds.take i)-p)‖ < R
  by_contra hn
  have he := hescape (p+displacement (ds.take i)) (le_of_not_gt hn)
  have hp := passageTime_le_cost w hw p (p+displacement (ds.take i)) (ds.take i) rfl
  have ht := pathCost_take_le w hw p ds i
  linarith

/-- Approximate passage-time minimizers with any positive error bound control
the cost of escaping a ball. -/
theorem exists_confined_near_optimal (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R a ε : ℝ) (hε : 0 < ε)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hshort : passageTime w p q + ε ≤ a) :
    ∃ ds, p+displacement ds=q ∧ pathCost w p ds < passageTime w p q+ε ∧
      PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  exact ⟨ds,hend,hcost,path_confined_of_escape w hw p ds R a hescape (hcost.trans_le hshort)⟩

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingLocalized
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

theorem mem_internalEdges (e : Edge) (V : Finset Vertex) :
    e ∈ internalEdges V ↔ e.1 ∈ V ∧ edgeEnd e ∈ V := by
  simp [internalEdges]

theorem step_mem_internalEdges (V : Finset Vertex) (p : Vertex) (d : Step)
    (hp : p ∈ V) (hq : p+d.delta ∈ V) : d.edge p ∈ internalEdges V := by
  rw [mem_internalEdges]
  cases d <;> simp_all [Step.edge,Step.delta,edgeEnd,add_assoc]
  all_goals change p+0 ∈ V; simpa using hp

theorem internalEdges_disjoint {V W : Finset Vertex} (h : Disjoint V W) :
    Disjoint (internalEdges V) (internalEdges W) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp h (mem_internalEdges e V |>.mp he).1
    (mem_internalEdges e W |>.mp hf).1

theorem pathIn_cons_iff (p : Vertex) (d : Step) (ds : List Step) (S : Set Vertex) :
    PathIn p (d::ds) S ↔ p ∈ S ∧ PathIn (p+d.delta) ds S := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp),?_⟩
    intro i hi
    have hh := h (i+1) (by simpa using hi)
    simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh
  · rintro ⟨hp,ht⟩ i hi
    cases i with
    | zero => simpa using hp
    | succ i =>
      have hh := ht i (by simpa using hi)
      simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh

theorem pathEdges_subset_internalEdges (V : Finset Vertex) (p : Vertex) (ds : List Step)
    (h : PathIn p ds (V : Set Vertex)) : pathEdges p ds ⊆ internalEdges V := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds _).mp h
    have hq : p+d.delta ∈ V := by simpa using ht 0 (by omega)
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he]
      exact step_mem_internalEdges V p d hp hq
    · exact ih (p+d.delta) ht he

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges,he]))]

theorem measurableSet_strictLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (strictLocalizedEvent V family bound) := by
  simpa only [strictLocalizedEvent,and_assoc] using
    measurableSet_strict_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem strictLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (strictLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

theorem strip_vertices_disjoint (V W : Finset Vertex) (b y z R : ℝ)
    (hV : ∀ v ∈ V, |transverse b v-y| ≤ R)
    (hW : ∀ v ∈ W, |transverse b v-z| ≤ R)
    (hsep : 2*R < |y-z|) : Disjoint V W := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have ht := abs_add_le (y-transverse b v) (transverse b v-z)
  rw [sub_add_sub_cancel,abs_sub_comm y (transverse b v)] at ht
  have h1 := hV v hv
  have h2 := hW v hw
  linarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKPrimitives
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.BK
open PlanarFPP Finset

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges, GammaFPP.CrossingBridge.pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges, GammaFPP.CrossingBridge.pathEdges,he]))]

lemma dyadicSurvival_mono (t : ℕ) {x y : Finset (Edge × Fin t)} (hxy : x ⊆ y) (e : Edge) :
    dyadicSurvival t x e ≤ dyadicSurvival t y e := by
  apply Finset.sum_le_sum
  intro h _
  by_cases hx : (e,h) ∈ x
  · simp [hx,hxy hx]
  · simp only [hx,↓reduceIte]
    split_ifs <;> positivity

lemma dyadicSurvival_eq (t : ℕ) (x y : Finset (Edge × Fin t)) (e : Edge)
    (h : ∀ a : Fin t, (e,a) ∈ x ↔ (e,a) ∈ y) :
    dyadicSurvival t x e = dyadicSurvival t y e := by
  apply Finset.sum_congr rfl
  intro a _
  simp only [h a]

lemma pathCost_le_of_edges {w v : Edge → ℝ} (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e ≤ v e) : pathCost w p ds ≤ pathCost v p ds := by
  induction ds generalizing p with
  | nil => exact le_rfl
  | cons d ds ih =>
    exact add_le_add (h _ (by simp [pathEdges, GammaFPP.CrossingBridge.pathEdges]))
      (ih _ (fun e he => h e (by simp [pathEdges, GammaFPP.CrossingBridge.pathEdges,he])))

lemma StrictPathWitness.disjoint_bits {p q : StrictPathWitness} (t : ℕ)
    (h : Disjoint p.edges q.edges) : Disjoint (p.bits t) (q.bits t) := by
  apply Finset.disjoint_left.mpr
  intro a hp hq
  exact Finset.disjoint_left.mp h (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hq).1

lemma dyadicRank_sum (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e = ∑ h : Fin t, if (e,h) ∈ x then 2^(t-(h.val+1)) else 0 := by
  unfold dyadicRank dyadicPositions
  rw [sum_image]
  · simp only [sum_filter]
  · intro a _ b _ hab
    change t-(a.val+1)=t-(b.val+1) at hab
    apply Fin.ext
    have := a.isLt
    have := b.isLt
    omega

/-- Exact binary representation of the source rounded survival probability. -/
lemma dyadicSurvival_eq_rank (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicSurvival t x e = (dyadicRank t x e : ℝ)/(2:ℝ)^t := by
  rw [dyadicRank_sum]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero]
  rw [Finset.sum_div]
  unfold dyadicSurvival
  apply sum_congr rfl
  intro h _
  by_cases hm : (e,h) ∈ x
  · simp only [hm,↓reduceIte]
    have hh : t=(t-(h.val+1))+(h.val+1) := by omega
    have hp : (2:ℝ)^t = 2^(t-(h.val+1))*2^(h.val+1) := by rw [← pow_add,← hh]
    rw [hp]
    field_simp
  · simp [hm]

end GammaFPP.BK

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SurvivalRounding
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open Set Filter
open scoped Topology ENNReal
variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

lemma gammaRoundedSurvival_le (hs : 0 < shape) (hr : 0 < rate) (t : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gammaRoundedSurvival (shape := shape) (rate := rate) t x ≤ gammaSurvival shape rate x := by
  rw [gammaRoundedSurvival, div_le_iff₀ (by positivity)]
  have hp := (gammaSurvival_mem hs hr hx).1.le
  simpa only [mul_comm] using Nat.floor_le
    (show 0 ≤ (2 : ℝ)^t * gammaSurvival shape rate x by positivity)

lemma gammaRoundedSurvival_tendsto (hs : 0 < shape) (hr : 0 < rate) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun t => gammaRoundedSurvival (shape := shape) (rate := rate) t x)
      atTop (𝓝 (gammaSurvival shape rate x)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (gammaSurvival_mem hs hr hx).1.le).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  simpa [gammaRoundedSurvival, Function.comp_def, mul_comm] using h

lemma gammaRoundedSurvival_eventually_pos (hs : 0 < shape) (hr : 0 < rate) {x : ℝ} (hx : 0 ≤ x) :
    ∀ᶠ t in atTop, 0 < gammaRoundedSurvival (shape := shape) (rate := rate) t x :=
  (gammaRoundedSurvival_tendsto hs hr hx).eventually
    (lt_mem_nhds (gammaSurvival_mem hs hr hx).1)

lemma gammaRoundedCost_ge (t : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hp : 0 < gammaRoundedSurvival (shape := shape) (rate := rate) t x) :
    x ≤ gammaRoundedCost hs hr t x :=
  gammaSurvivalQuantile_upper_cost hs hr hx hp (gammaRoundedSurvival_le hs hr t hx)

lemma gammaRoundedCost_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun t => gammaRoundedCost hs hr t x) atTop (𝓝 x) := by
  have hS := gammaSurvival_mem hs hr hx
  have hw : Tendsto (fun t => gammaRoundedSurvival (shape := shape) (rate := rate) t x)
      atTop (𝓝[Ioc (0 : ℝ) 1] (gammaSurvival shape rate x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨gammaRoundedSurvival_tendsto hs hr hx, ?_⟩
    filter_upwards [gammaRoundedSurvival_eventually_pos hs hr hx] with t ht
    exact ⟨ht, (gammaRoundedSurvival_le hs hr t hx).trans hS.2⟩
  have h := ((gammaSurvivalQuantile_continuousOn hs hr) _ hS).tendsto.comp hw
  simpa only [gammaSurvivalQuantile_inverse hs hr hx, gammaRoundedCost,
    Function.comp_def] using h

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKDyadic
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.BK
open PlanarFPP Finset Set

lemma survival_le_one (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicSurvival t x e ≤ 1 := by
  rw [dyadicSurvival_eq_rank, div_le_iff₀ (by positivity), one_mul]
  exact_mod_cast (GammaFPP.dyadicRank_lt t x e).le

lemma bitGood_mono {D : ℝ → ℝ} (hD : AntitoneOn D (Ioc 0 1))
    {t : ℕ} {x y : Finset (Edge × Fin t)} {p : StrictPathWitness}
    (h : BitGood D t x p) (hxy : x ⊆ y) : BitGood D t y p := by
  constructor
  · intro e he
    exact (h.1 e he).trans_le (dyadicSurvival_mono t hxy e)
  · apply lt_of_le_of_lt (pathCost_le_of_edges p.start p.steps ?_) h.2
    intro e he
    exact hD ⟨h.1 e he, survival_le_one t x e⟩
      ⟨(h.1 e he).trans_le (dyadicSurvival_mono t hxy e), survival_le_one t y e⟩
      (dyadicSurvival_mono t hxy e)

lemma bitGood_of_agree {D : ℝ → ℝ} {t : ℕ}
    {x y : Finset (Edge × Fin t)} {p : StrictPathWitness}
    (h : BitGood D t x p)
    (hxy : ∀ a ∈ p.bits t, a ∈ y ↔ a ∈ x) : BitGood D t y p := by
  have heq : ∀ e ∈ p.edges, dyadicSurvival t y e = dyadicSurvival t x e := by
    intro e he
    exact dyadicSurvival_eq t y x e (fun a => hxy (e,a) (by
      simpa only [StrictPathWitness.bits, Finset.mem_product, Finset.mem_univ, and_true] using he))
  constructor
  · intro e he
    rw [heq e he]
    exact h.1 e he
  · have hc := pathCost_eq_of_agree
      (fun e => D (dyadicSurvival t y e)) (fun e => D (dyadicSurvival t x e))
      p.start p.steps (fun e he => congrArg D (heq e he))
    rw [hc]
    exact h.2

lemma mem_bitFamily (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (F : Set StrictPathWitness) (x : Finset (Edge × Fin t)) :
    x ∈ bitFamily D S t F ↔ x ⊆ S.product (Finset.univ : Finset (Fin t)) ∧
      ∃ p ∈ F, p.edges ⊆ S ∧ BitGood D t x p := by
  classical
  simp only [bitFamily, Finset.mem_filter, Finset.mem_powerset]

lemma upward_bitFamily {D : ℝ → ℝ} (hD : AntitoneOn D (Ioc 0 1))
    (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    UpwardFamily (S.product (Finset.univ : Finset (Fin t))) (bitFamily D S t F) := by
  constructor
  · intro x hx
    exact ((mem_bitFamily ..).mp hx).1
  · intro x hx y hxy hys
    obtain ⟨_,p,hp,he,hg⟩ := (mem_bitFamily ..).mp hx
    exact (mem_bitFamily ..).mpr ⟨hys,p,hp,he,bitGood_mono hD hg hxy⟩

lemma bit_path_forces (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (F : Set StrictPathWitness) (x : Finset (Edge × Fin t)) (p : StrictPathWitness)
    (hp : p ∈ F) (he : p.edges ⊆ S) (hg : BitGood D t x p) :
    ForcesBits (S.product (Finset.univ : Finset (Fin t))) (bitFamily D S t F) x (p.bits t) := by
  intro y hys hxy
  exact (mem_bitFamily ..).mpr ⟨hys,p,hp,he,bitGood_of_agree hg hxy⟩

/-- Repeated labelled families are allowed: independence of events is not assumed. -/
theorem decoder_finite_path_BK {D : ℝ → ℝ} (hD : AntitoneOn D (Ioc 0 1))
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitDisjointFamily D S t Fs) ≤
      (Fs.map (fun F => fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitFamily D S t F))).prod := by
  apply (finite_fair_BK_forcing (S.product (Finset.univ : Finset (Fin t))) (Fs.map (bitFamily D S t))
    (bitDisjointFamily D S t Fs) ?_ ?_).trans_eq
      (by simp only [List.map_map,Function.comp_def])
  · intro A hA
    obtain ⟨F,_,rfl⟩ := List.mem_map.mp hA
    exact upward_bitFamily hD S t F
  · intro x hx
    simp only [bitDisjointFamily,Finset.mem_filter,Finset.mem_powerset] at hx
    obtain ⟨hxs,ps,hps,hd⟩ := hx
    refine ⟨hxs,ps.map (fun p => p.bits t),?_,?_⟩
    · clear hd
      induction hps with
      | nil => exact List.Forall₂.nil
      | cons h ht ih =>
        exact List.Forall₂.cons (bit_path_forces D S t _ x _ h.1 h.2.1 h.2.2) ih
    · rw [List.pairwise_map]
      exact hd.imp (fun h => StrictPathWitness.disjoint_bits t h)

/-- Actual Gamma decoder, for every positive shape and rate. -/
theorem gamma_decoder_finite_path_BK {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs) ≤
      (Fs.map (fun F => fairFamilyMass (S.product (Finset.univ : Finset (Fin t)))
        (bitFamily (gammaSurvivalQuantile hs hr) S t F))).prod :=
  decoder_finite_path_BK (gammaSurvivalQuantile_antitoneOn hs hr) S t Fs
end GammaFPP.BK

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKRounded
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.BK
open PlanarFPP MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology ENNReal
variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

lemma rounded_original {t : ℕ} {w : Edge → ℝ} {p : StrictPathWitness}
    (hw : ∀ e, 0 ≤ w e) (h : RoundedGood hs hr t w p) : p.Good w := by
  exact lt_of_le_of_lt (pathCost_le_of_edges p.start p.steps
    (fun e he => gammaRoundedCost_ge hs hr t (hw e) (h.1 e he))) h.2

lemma rounded_path_tendsto (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) :
    Tendsto (fun t => pathCost (fun e => gammaRoundedCost hs hr t (w e)) p ds)
      atTop (𝓝 (pathCost w p ds)) := by
  induction ds generalizing p with
  | nil => exact tendsto_const_nhds
  | cons d ds ih => exact (gammaRoundedCost_tendsto hs hr (hw (d.edge p))).add (ih _)

lemma eventually_rounded {w : Edge → ℝ} (hw : ∀ e, 0 ≤ w e)
    {p : StrictPathWitness} (h : p.Good w) :
    ∀ᶠ t in atTop, RoundedGood hs hr t w p := by
  have he : ∀ᶠ t in atTop, ∀ e ∈ p.edges,
      0 < gammaRoundedSurvival (shape := shape) (rate := rate) t (w e) := by
    rw [Filter.eventually_all_finset]
    intro e _
    exact gammaRoundedSurvival_eventually_pos hs hr (hw e)
  exact he.and ((rounded_path_tendsto hs hr w hw p.start p.steps).eventually (gt_mem_nhds h))

lemma list_eventually_rounded (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (ps : List StrictPathWitness) (h : ∀ p ∈ ps, p.Good w) :
    ∀ᶠ t in atTop, ∀ p ∈ ps, RoundedGood hs hr t w p := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := eventually_rounded hs hr hw (h p (List.mem_cons_self ..))
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    filter_upwards [hp,ht] with t hp ht q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact ht q hq

lemma disjoint_eventually_rounded {S : Finset Edge} {Fs : List (Set StrictPathWitness)}
    {w : Edge → ℝ} (hw : ∀ e, 0 ≤ w e) (h : StrictDisjointPaths S Fs w) :
    ∀ᶠ t in atTop, RoundedDisjoint hs hr S Fs t w := by
  obtain ⟨ps,hps,hd⟩ := h
  have hg : ∀ p ∈ ps, p.Good w := by
    clear hd
    induction hps with
    | nil => simp
    | cons hp hps ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp.2.2
      · exact ih q hq
  filter_upwards [list_eventually_rounded hs hr w hw ps hg] with t ht
  refine ⟨ps,?_,hd⟩
  clear hd hg
  induction hps with
  | nil => exact List.Forall₂.nil
  | @cons p F ps Fs hp hps ih =>
    exact List.Forall₂.cons ⟨hp.1,hp.2.1,ht p (List.mem_cons_self ..)⟩
      (ih (fun q hq => ht q (List.mem_cons_of_mem _ hq)))

variable {Ω : Type*} {τ : Edge → Ω → ℝ}

lemma cell_survival {S : Finset Edge} {t : ℕ} {x : Finset (Edge × Fin t)}
    {ω : Ω} (hc : ω ∈ gammaDyadicRankCell shape rate τ S t x)
    {e : Edge} (he : e ∈ S) :
    gammaRoundedSurvival (shape := shape) (rate := rate) t (τ e ω) =
      dyadicSurvival t x e := by
  rw [gammaRoundedSurvival, hc e he, dyadicSurvival_eq_rank]

lemma cell_path_iff {S : Finset Edge} {t : ℕ} {x : Finset (Edge × Fin t)}
    {ω : Ω} (hc : ω ∈ gammaDyadicRankCell shape rate τ S t x)
    (p : StrictPathWitness) (hp : p.edges ⊆ S) :
    RoundedGood hs hr t (fun e => τ e ω) p ↔
      BitGood (gammaSurvivalQuantile hs hr) t x p := by
  have heq : ∀ e ∈ p.edges,
      gammaRoundedSurvival (shape := shape) (rate := rate) t (τ e ω) =
        dyadicSurvival t x e := fun e he => cell_survival hc (hp he)
  have hh := pathCost_eq_of_agree
    (fun e => gammaRoundedCost hs hr t (τ e ω))
    (fun e => gammaSurvivalQuantile hs hr (dyadicSurvival t x e))
    p.start p.steps (fun e he => congrArg (gammaSurvivalQuantile hs hr) (heq e he))
  unfold RoundedGood BitGood
  rw [hh]
  apply and_congr_left
  intro _
  exact forall_congr' (fun e => forall_congr' (fun he => by rw [heq e he]))

end GammaFPP.BK

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.BK
open MeasureTheory Set Filter
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Generic outer-measure limit with AE support capture. No measurability of
an uncountable witness-label union or monotonicity of Rounded_t is assumed. -/
lemma ae_eventual_measure_le (P : Measure Ω) (A : Set Ω) (R : ℕ → Set Ω)
    (C : ℝ≥0∞) (hcap : ∀ᵐ ω ∂P, ω ∈ A → ∀ᶠ t in atTop, ω ∈ R t)
    (hbound : ∀ t, P (R t) ≤ C) : P A ≤ C := by
  let E : ℕ → Set Ω := fun N => ⋂ t ≥ N, R t
  have hsubset : A ≤ᵐ[P] ⋃ N, E N := by
    filter_upwards [hcap] with ω hω
    intro ha
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hω ha)
    exact Set.mem_iUnion.mpr ⟨N,Set.mem_iInter.mpr (fun t => Set.mem_iInter.mpr (hN t))⟩
  have hmono : Monotone E := by
    intro N M hNM ω hω
    simp only [E,mem_iInter] at hω ⊢
    exact fun t ht => hω t (hNM.trans ht)
  have hE : ∀ N, P (E N) ≤ C := by
    intro N
    apply (measure_mono ?_).trans (hbound N)
    intro ω hω
    exact mem_iInter.mp (mem_iInter.mp hω N) le_rfl
  calc
    P A ≤ P (⋃ N, E N) := measure_mono_ae hsubset
    _ = ⨆ N, P (E N) := hmono.measure_iUnion
    _ ≤ C := iSup_le hE

end GammaFPP.BK

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.BK
open MeasureTheory ProbabilityTheory Set Finset Filter PlanarFPP
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

lemma bitFamily_subset (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (F : Set StrictPathWitness) : bitFamily D S t F ⊆ (S.product (Finset.univ : Finset (Fin t))).powerset := by
  intro x hx
  exact Finset.mem_powerset.mpr ((mem_bitFamily ..).mp hx).1

lemma bitDisjointFamily_subset (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) :
    bitDisjointFamily D S t Fs ⊆ (S.product (Finset.univ : Finset (Fin t))).powerset := by
  classical
  exact Finset.filter_subset _ _

lemma single_mass_le (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitFamily (gammaSurvivalQuantile hs hr) S t F) ≤
      P.real {ω | StrictPathEvent S F (fun e => τ e ω)} := by
  let _ := h.probability
  have hmass : P.real (⋃ x ∈ bitFamily (gammaSurvivalQuantile hs hr) S t F,
      gammaDyadicRankCell shape rate τ S t x) =
      fairFamilyMass (S.product (Finset.univ : Finset (Fin t)))
        (bitFamily (gammaSurvivalQuantile hs hr) S t F) := by
    simpa only [Finset.product_eq_sprod] using
      h.gammaDyadicRankCells_real hs hr S t
        (bitFamily (gammaSurvivalQuantile hs hr) S t F)
        (bitFamily_subset (gammaSurvivalQuantile hs hr) S t F)
  rw [← hmass]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h.ae_positive] with ω hpos
  intro hω
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hx,hcell⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_,p,hp,he,hgood⟩ := (mem_bitFamily ..).mp hx
  exact ⟨p,hp,he,rounded_original hs hr (fun e => (hpos e).le)
    ((cell_path_iff hs hr hcell p he).mpr hgood)⟩

lemma rounded_disjoint_mass_le (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) :
    P.real {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)} ≤
      fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs) := by
  classical
  let _ := h.probability
  have hmass : P.real (⋃ x ∈ bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs,
      gammaDyadicRankCell shape rate τ S t x) =
      fairFamilyMass (S.product (Finset.univ : Finset (Fin t)))
        (bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs) := by
    simpa only [Finset.product_eq_sprod] using
      h.gammaDyadicRankCells_real hs hr S t
        (bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs)
        (bitDisjointFamily_subset (gammaSurvivalQuantile hs hr) S t Fs)
  rw [← hmass]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h.ae_gammaDyadicRankCell hs hr S t] with ω hω
  intro hd
  obtain ⟨x,hx,hcell⟩ := hω
  obtain ⟨ps,hps,hdis⟩ := hd
  have hmem : x ∈ bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs := by
    apply Finset.mem_filter.mpr
    refine ⟨hx,ps,?_,hdis⟩
    exact hps.imp (fun p _ hp =>
      ⟨hp.1,hp.2.1,(cell_path_iff hs hr hcell p hp.2.1).mp hp.2.2⟩)
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hmem,hcell⟩⟩

lemma probabilities_nonneg (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    0 ≤ (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  induction Fs with
  | nil => simp
  | cons F Fs ih => exact mul_nonneg measureReal_nonneg ih

lemma factors_le (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    (Fs.map (fun F => fairFamilyMass (S.product (Finset.univ : Finset (Fin t)))
      (bitFamily (gammaSurvivalQuantile hs hr) S t F))).prod ≤
    (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  induction Fs with
  | nil => simp
  | cons F Fs ih =>
    simp only [List.map_cons,List.prod_cons]
    exact (mul_le_mul_of_nonneg_left ih (fairFamilyMass_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right (single_mass_le h hs hr S t F)
        (probabilities_nonneg (P := P) (τ := τ) S Fs))

theorem gamma_rounded_strict_path_BK (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) :
    P.real {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)} ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod :=
  (rounded_disjoint_mass_le h hs hr S t Fs).trans
    ((gamma_decoder_finite_path_BK hs hr S t Fs).trans (factors_le h hs hr S t Fs))

/-- Finite-path repeated BK in the actual Gamma environment, for every
positive real shape and rate. Fs may repeat and regions may overlap; only the
chosen paths' undirected edge sets must be pairwise disjoint. -/
theorem gamma_strict_path_BK (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset Edge)
    (Fs : List (Set StrictPathWitness)) :
    P.real {ω | StrictDisjointPaths S Fs (fun e => τ e ω)} ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  let _ := h.probability
  let C : ℝ := (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod
  have hC : 0 ≤ C := probabilities_nonneg (P := P) (τ := τ) S Fs
  have hh := ae_eventual_measure_le P
    {ω | StrictDisjointPaths S Fs (fun e => τ e ω)}
    (fun t => {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)})
    (ENNReal.ofReal C) (by
      filter_upwards [h.ae_positive] with ω hpos
      intro hω
      exact disjoint_eventually_rounded hs hr (fun e => (hpos e).le) hω) (fun t => by
        calc
          P {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)} =
              ENNReal.ofReal (P.real {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)}) :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal
            (gamma_rounded_strict_path_BK h hs hr S t Fs))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hC)
end GammaFPP.BK

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MovingOrigin
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem measurableSet_goodOrigin (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ) :
    MeasurableSet {w | GoodOrigin μ α C η δ n w} := by
  unfold GoodOrigin
  simp only [ofPred_and, ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun e => ?_) ?_
  · exact measurableSet_le measurable_const (measurable_pi_apply e)
  refine MeasurableSet.inter (MeasurableSet.iInter fun z => ?_)
    (MeasurableSet.iInter fun z => ?_)
  · apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (continuous_abs.measurable.comp ((measurable_passageTime measurable_pi_apply 0 z).sub_const _))
      measurable_const
  · apply MeasurableSet.iInter
    intro _
    exact measurableSet_le measurable_const (measurable_passageTime measurable_pi_apply 0 z)

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteWaypoints
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- A location-uniform finite union estimate. The common shape-test error is
at the fixed origin, while every tested location may be different. -/
theorem gamma_finite_waypoint_failure_bound
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    {ι : Type*} (J : Finset ι) (a : ι → Vertex) (C n : ℕ) (η δ : ℝ) :
    P.real {ω | ∃ j ∈ J, ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)} ≤
      (J.card : ℝ) * P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C η δ n (fun e => τ e ω)} := by
  classical
  let := h.probability
  let A (j : ι) := {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
    (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)}
  have hevent : {ω | ∃ j ∈ J, ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a j) e) ω)} =
      ⋃ j ∈ J, A j := by
    ext ω
    constructor
    · rintro ⟨j, hj, hω⟩
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hω⟩⟩
    · intro hω
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hω
      obtain ⟨hJ, hgood⟩ := Set.mem_iUnion.mp hj
      exact ⟨j, hJ, hgood⟩
  rw [hevent]
  have he (j : ι) : P.real (A j) =
      P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C η δ n (fun e => τ e ω)} := by
    exact congrArg ENNReal.toReal (h.translated_event_probability (a j)
      {w | ¬GoodOrigin (gammaMeanNorm h hs hr) (cheapSlope shape rate) C η δ n w}
      (measurableSet_goodOrigin _ _ _ _ _ n).compl)
  calc
    _ ≤ ∑ j ∈ J, P.real (A j) := measureReal_biUnion_finset_le J A
    _ = _ := by simp only [he, sum_const, nsmul_eq_mul]

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PathChain
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

theorem pathIn_append (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (hd : PathIn p ds S) (he : PathIn (p+displacement ds) es S) :
    PathIn p (ds++es) S := by
  intro i hi
  by_cases hid : i ≤ ds.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le hid, List.take_zero,
      List.append_nil] using hd i hid
  · have hle : ds.length ≤ i := by omega
    have hie : i-ds.length ≤ es.length := by simp only [List.length_append] at hi; omega
    have hh := he (i-ds.length) hie
    simpa only [List.take_append, List.take_of_length_le hle, displacement_append,
      add_assoc] using hh

/-- Concatenating a finite list of connections preserves vertex localization and adds traversal costs. -/
theorem exists_path_chain (w : Edge → ℝ) (p : ℕ → Vertex) (S : Set Vertex)
    (a : ℕ → ℝ) (n : ℕ) (hp : p 0 ∈ S)
    (h : ∀ i < n, ∃ ds, p i+displacement ds=p (i+1) ∧
      pathCost w (p i) ds ≤ a i ∧ PathIn (p i) ds S) :
    ∃ ds, p 0+displacement ds=p n ∧
      pathCost w (p 0) ds ≤ ∑ i ∈ range n, a i ∧ PathIn (p 0) ds S := by
  induction n with
  | zero =>
    refine ⟨[],by simp,by simp [pathCost],?_⟩
    intro i hi
    simpa using hp
  | succ n ih =>
    obtain ⟨ds,hd,hcostd,hind⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨es,he,hcoste,hine⟩ := h n (Nat.lt_succ_self n)
    refine ⟨ds++es,?_,?_,?_⟩
    · rw [displacement_append, ← add_assoc, hd]
      exact he
    · rw [pathCost_append, hd, sum_range_succ]
      exact add_le_add hcostd hcoste
    · apply pathIn_append _ _ _ _ hind
      simpa only [hd] using hine

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Waypoints
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

theorem waypoint_end (p q : Vertex) (B : ℕ) (hB : 0 < B) : waypoint p q B B=q := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  simp [waypoint,segmentPoint,hb]

theorem waypoint_error (p q : Vertex) (B j : ℕ) :
    ‖latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B)‖ ≤ 2 :=
  latticeFloor_error _

theorem waypoint_displacement_error (p q : Vertex) (B j : ℕ) :
    ‖latticeEmbed (waypoint p q B (j+1)-waypoint p q B j) -
      (1/(B : ℝ)) • latticeEmbed (q-p)‖ ≤ 4 := by
  have he : latticeEmbed (waypoint p q B (j+1)-waypoint p q B j) -
      (1/(B : ℝ)) • latticeEmbed (q-p) =
      (latticeEmbed (waypoint p q B (j+1))-segmentPoint p q (((j+1 : ℕ) : ℝ)/B)) -
      (latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B)) := by
    rw [latticeEmbed_sub,latticeEmbed_sub]
    unfold segmentPoint
    ext i
    simp [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [waypoint_error p q B (j+1),waypoint_error p q B j])

theorem waypoint_displacement_norm (p q : Vertex) (B j : ℕ) (hB : 0 < B) :
    ‖latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)‖ ≤
      ‖latticeEmbed (q-p)‖/(B : ℝ)+4 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hn := norm_add_le
    (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)-(1/(B : ℝ)) • latticeEmbed (q-p))
    ((1/(B : ℝ)) • latticeEmbed (q-p))
  rw [sub_add_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hb)] at hn
  have he := waypoint_displacement_error p q B j
  have hid : (1/(B : ℝ))*‖latticeEmbed (q-p)‖=‖latticeEmbed (q-p)‖/(B : ℝ) := by ring
  rw [hid] at hn
  linarith

theorem waypoint_cost_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (β : ℝ) (hβ : 0 ≤ β) (hlip : ∀ v w, |μ v-μ w| ≤ β*‖v-w‖)
    (p q : Vertex) (B j : ℕ) (hB : 0 < B) :
    μ (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)) ≤
      μ (latticeEmbed (q-p))/(B : ℝ)+4*β := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have ht := (le_abs_self _).trans (hlip
    (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j))
    ((1/(B : ℝ)) • latticeEmbed (q-p)))
  have he := mul_le_mul_of_nonneg_left (waypoint_displacement_error p q B j) hβ
  rw [hμ.homogeneous,abs_of_pos (one_div_pos.mpr hb)] at ht
  have hid : (1/(B : ℝ))*μ (latticeEmbed (q-p))=μ (latticeEmbed (q-p))/(B : ℝ) := by ring
  rw [hid] at ht
  linarith

theorem waypoint_ball_in_tube (p q : Vertex) (B j : ℕ) (hB : 0 < B) (hj : j ≤ B)
    (R : ℝ) (z : Vertex) (hz : ‖latticeEmbed (z-waypoint p q B j)‖ ≤ R) :
    z ∈ SegmentTube p q (R+2) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  refine ⟨(j : ℝ)/B,div_nonneg (Nat.cast_nonneg _) hb.le,?_,?_⟩
  · exact (div_le_one hb).mpr (by exact_mod_cast hj)
  have he := waypoint_error p q B j
  have ht := norm_add_le (latticeEmbed z-latticeEmbed (waypoint p q B j))
    (latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B))
  rw [sub_add_sub_cancel] at ht
  rw [latticeEmbed_sub] at hz
  linarith

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TubeDeterministic
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

theorem localTravel_of_waypoint_tests (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (β : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q : Vertex) (B C n : ℕ) (hB : 0 < B) (α D η δ κ : ℝ)
    (hdist : ‖latticeEmbed (q-p)‖ ≤ D*n)
    (hshortdist : D*n/(B : ℝ)+4 ≤ (C : ℝ)*n)
    (hshortcost : β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6)
    (htotal : (B : ℝ)*(4*β+κ*n+1) ≤ η*n)
    (htube : δ*n/3+2 ≤ δ*n)
    (hgood : ∀ j < B, GoodOrigin μ α C κ δ n
      (fun e => w (shiftEdge (waypoint p q B j) e))) :
    LocalTravel μ η δ n p q w := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hw : ∀ e, 0 ≤ w e := by
    intro e
    have ht := (hgood 0 hB).1 (e.1-p,e.2)
    simpa [waypoint_zero,shiftEdge] using ht
  have hμzero : μ 0=0 := (hμ.zero_iff 0).mpr rfl
  have hwhole : μ (latticeEmbed (q-p)) ≤ β*(D*n) := by
    have ht := (le_abs_self _).trans (hlip (latticeEmbed (q-p)) 0)
    simp only [hμzero,sub_zero] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hdist hβ)
  let a := μ (latticeEmbed (q-p))/(B : ℝ)+4*β+κ*n+1
  have hpiece (j : ℕ) (hj : j < B) : ∃ ds,
      waypoint p q B j+displacement ds=waypoint p q B (j+1) ∧
      pathCost w (waypoint p q B j) ds ≤ a ∧
      PathIn (waypoint p q B j) ds (SegmentTube p q (δ*n)) := by
    let x := waypoint p q B j
    let y := waypoint p q B (j+1)
    have hg := hgood j hj
    have hlength : ‖latticeEmbed (y-x)‖ ≤ (C : ℝ)*n := by
      have ht := waypoint_displacement_norm p q B j hB
      exact (ht.trans (add_le_add ((div_le_div_iff_of_pos_right hb).mpr hdist) le_rfl)).trans hshortdist
    have herror := (abs_le.mp (hg.2.1 (y-x) hlength)).2
    have hpassage : passageTime w x y ≤ μ (latticeEmbed (y-x))+κ*n := by
      have hxy : waypoint p q B j+(y-x)=y := by dsimp [x]; abel
      simp only [passageTime_translate,add_zero,hxy] at herror
      linarith
    have hstepμ := waypoint_cost_bound μ hμ β hβ hlip p q B j hB
    have hshort : passageTime w x y+1 ≤ α*δ*n/6 := by
      have hd := (div_le_div_iff_of_pos_right hb).mpr hwhole
      change μ (latticeEmbed (y-x)) ≤ _ at hstepμ
      linarith
    have hescape (z : Vertex) (hz : δ*n/3 ≤ ‖latticeEmbed (z-x)‖) :
        α*δ*n/6 ≤ passageTime w x z := by
      have hxz : waypoint p q B j+(z-x)=z := by dsimp [x]; abel
      simpa only [passageTime_translate,add_zero,hxz] using hg.2.2 (z-x) hz
    obtain ⟨ds,hend,hcost,hlocal⟩ := exists_confined_near_optimal w hw x y
      (δ*n/3) (α*δ*n/6) 1 (by norm_num) hescape hshort
    refine ⟨ds,hend,?_,?_⟩
    · change pathCost w x ds ≤ a
      dsimp [a]
      change μ (latticeEmbed (y-x)) ≤ _ at hstepμ
      linarith
    · intro i hi
      obtain ⟨t,ht0,ht1,hbound⟩ := waypoint_ball_in_tube p q B j hB hj.le
        (δ*n/3) (x+displacement (ds.take i)) (hlocal i hi).le
      exact ⟨t,ht0,ht1,hbound.trans htube⟩
  have hp : waypoint p q B 0 ∈ SegmentTube p q (δ*n) := by
    refine ⟨0,by norm_num,by norm_num,?_⟩
    have hn : 0 ≤ δ*n := by linarith
    simpa [segmentPoint] using hn
  obtain ⟨ds,hend,hcost,hlocal⟩ := exists_path_chain w (waypoint p q B)
    (SegmentTube p q (δ*n)) (fun _ => a) B hp hpiece
  refine ⟨ds,by simpa [waypoint_end p q B hB] using hend,?_,by simpa using hlocal⟩
  have hid : (B : ℝ)*a=μ (latticeEmbed (q-p))+(B : ℝ)*(4*β+κ*n+1) := by
    dsimp [a]
    field_simp; ring
  simp only [sum_const,card_range,nsmul_eq_mul] at hcost
  rw [hid] at hcost
  simpa only [waypoint_zero] using hcost.trans (add_le_add le_rfl htotal)

theorem localTravel_parameters (α β D η δ : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ B C : ℕ, ∃ κ : ℝ, 0 < B ∧ 0 < C ∧ 0 < κ ∧
      ∀ᶠ n : ℕ in atTop,
        D*n/(B : ℝ)+4 ≤ (C : ℝ)*n ∧
        β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6 ∧
        (B : ℝ)*(4*β+κ*n+1) ≤ η*n ∧ δ*n/3+2 ≤ δ*n := by
  have had : 0 < α*δ := mul_pos hα hδ
  obtain ⟨B,hB⟩ := exists_nat_gt (max 1 (24*β*D/(α*δ)))
  have hb1 : (1 : ℝ) < B := (le_max_left _ _).trans_lt hB
  have hbpos : (0 : ℝ) < B := by linarith
  have hb : 0 < B := by exact_mod_cast hbpos
  have hbchoose := (div_lt_iff₀ had).mp ((le_max_right _ _).trans_lt hB)
  have hbase : β*D/(B : ℝ) ≤ α*δ/24 :=
    (div_le_iff₀ hbpos).mpr (by nlinarith)
  obtain ⟨C,hC⟩ := exists_nat_gt (D+4)
  have hc : 0 < C := by
    have : (0 : ℝ) < C := by linarith
    exact_mod_cast this
  let κ := min (η/(4*(B : ℝ))) (α*δ/24)
  have hk : 0 < κ := lt_min (div_pos hη (by linarith)) (div_pos had (by norm_num))
  have hkcost : κ ≤ α*δ/24 := min_le_right _ _
  have hktotal : (B : ℝ)*κ ≤ η/4 := by
    have ht := (le_div_iff₀ (by linarith : 0 < 4*(B : ℝ))).mp (min_le_left _ _ : κ ≤ η/(4*(B : ℝ)))
    nlinarith
  refine ⟨B,C,κ,hb,hc,hk,?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (12*(4*β+1)/(α*δ))),
    hlim.eventually (eventually_ge_atTop (2*(B : ℝ)*(4*β+1)/η)),
    hlim.eventually (eventually_ge_atTop (3/δ))] with n hn hn1 hn2 hn3
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1' := (div_le_iff₀ had).mp hn1
  have hn2' := (div_le_iff₀ hη).mp hn2
  have hn3' := (div_le_iff₀ hδ).mp hn3
  have hbase' := mul_le_mul_of_nonneg_right hbase hn0
  have hkcost' := mul_le_mul_of_nonneg_right hkcost hn0
  have hktotal' := mul_le_mul_of_nonneg_right hktotal hn0
  have hdiv : D*(n : ℝ)/(B : ℝ) ≤ D*n := by
    apply (div_le_iff₀ hbpos).mpr
    have ht := mul_le_mul_of_nonneg_left hb1.le (mul_nonneg hD.le hn0)
    simpa using ht
  have hc' := mul_le_mul_of_nonneg_right hC.le hn0
  have hid : β*(D*n)/(B : ℝ) = (β*D/(B : ℝ))*n := by ring
  rw [hid]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TubeTravel
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem gamma_tube_failure_bound
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (β : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |gammaMeanNorm h hs hr v-gammaMeanNorm h hs hr u| ≤ β*‖v-u‖)
    (p q : Vertex) (B C n : ℕ) (hB : 0 < B) (D η δ κ : ℝ)
    (hdist : ‖latticeEmbed (q-p)‖ ≤ D*n)
    (hshortdist : D*n/(B : ℝ)+4 ≤ (C : ℝ)*n)
    (hshortcost : β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ cheapSlope shape rate*δ*n/6)
    (htotal : (B : ℝ)*(4*β+κ*n+1) ≤ η*n)
    (htube : δ*n/3+2 ≤ δ*n) :
    P.real {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} ≤
      (B : ℝ)*P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C κ δ n (fun e => τ e ω)} := by
  let := h.probability
  have hsub : {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} ⊆
      {ω | ∃ j ∈ range B, ¬GoodOrigin (gammaMeanNorm h hs hr)
        (cheapSlope shape rate) C κ δ n (fun e => τ (shiftEdge (waypoint p q B j) e) ω)} := by
    intro ω hω
    by_contra hn
    apply hω
    apply localTravel_of_waypoint_tests _ _ (gammaMeanNorm_laws h hs hr) β hβ hlip
      p q B C n hB (cheapSlope shape rate) D η δ κ hdist hshortdist hshortcost htotal htube
    intro j hj
    by_contra hjbad
    exact hn ⟨j, mem_range.mpr hj, hjbad⟩
  refine (measureReal_mono hsub).trans ?_
  simpa only [card_range] using gamma_finite_waypoint_failure_bound h hs hr
    (range B) (waypoint p q B) C n κ δ

/-- Uniform probability statement for all deterministic endpoint pairs at each
large integer scale. It is NOT one event of simultaneous success for all pairs. -/
theorem gamma_tube_travel_nat
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ p q : Vertex,
      ‖latticeEmbed (q-p)‖ ≤ D*n →
      P.real {ω | ¬LocalTravel (gammaMeanNorm h hs hr) η δ n p q (fun e => τ e ω)} < ε := by
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound _ (gammaMeanNorm_laws h hs hr)
  obtain ⟨B,C,κ,hB,hC,hκ,hparams⟩ := localTravel_parameters
    (cheapSlope shape rate) β D η δ (cheapSlope_pos hs hr) hβ.le hD hη hδ
  have ht := gamma_moving_goodOrigin_failure_tendsto h hs hr C hC κ δ hκ hδ
    (fun _ => (0 : Vertex))
  have ht' : Tendsto (fun n => (B : ℝ)*P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C κ δ n (fun e => τ e ω)}) atTop (𝓝 0) := by
    simpa only [shiftEdge, zero_add, mul_zero] using ht.const_mul (B : ℝ)
  intro ε hε
  filter_upwards [hparams, ht'.eventually (gt_mem_nhds hε)] with n hn hprob
  intro p q hpq
  exact (gamma_tube_failure_bound h hs hr β hβ.le hlip p q B C n hB D η δ κ hpq
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans_lt hprob

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointNet
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

theorem step_embed_norm_le (d : Step) : ‖latticeEmbed d.delta‖ ≤ 1 := by
  have h := plane_norm_le_coordinates (latticeEmbed d.delta)
  cases d <;> simpa [Step.delta, latticeEmbed] using h

theorem displacement_norm_le_length (ds : List Step) :
    ‖latticeEmbed (displacement ds)‖ ≤ (ds.length : ℝ) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [displacement_cons, latticeEmbed_add]
    have ht := norm_add_le (latticeEmbed d.delta) (latticeEmbed (displacement ds))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [step_embed_norm_le d]

theorem coordinatePath_length (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

theorem coordinatePath_prefix_bound (p q : Vertex) (i : ℕ) :
    ‖latticeEmbed (p+displacement ((coordinatePath p q).take i)-p)‖ ≤
      (latticeDistance p q : ℝ) := by
  simp only [add_sub_cancel_left]
  exact (displacement_norm_le_length _).trans (by
    exact_mod_cast (show ((coordinatePath p q).take i).length ≤ latticeDistance p q by
      rw [List.length_take, coordinatePath_length]; exact min_le_right _ _))

theorem segmentPoint_perturbation (p q p' q' : Vertex) (r t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r) :
    ‖segmentPoint p' q' t-segmentPoint p q t‖ ≤ r := by
  have he : segmentPoint p' q' t-segmentPoint p q t =
      (1-t) • latticeEmbed (p'-p)+t • latticeEmbed (q'-q) := by
    simp only [segmentPoint,latticeEmbed_sub]
    ext i
    simp [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he]
  have hn := norm_add_le ((1-t) • latticeEmbed (p'-p)) (t • latticeEmbed (q'-q))
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1-t),abs_of_nonneg ht0] at hn
  have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1-t by linarith)
  have h2 := mul_le_mul_of_nonneg_left hq ht0
  nlinarith

theorem segmentTube_perturbation (p q p' q' : Vertex) (r R : ℝ)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r) :
    SegmentTube p' q' R ⊆ SegmentTube p q (R+r) := by
  rintro z ⟨t,ht0,ht1,ht⟩
  refine ⟨t,ht0,ht1,?_⟩
  have hb := segmentPoint_perturbation p q p' q' r t ht0 ht1 hp hq
  have hn := norm_add_le (latticeEmbed z-segmentPoint p' q' t)
    (segmentPoint p' q' t-segmentPoint p q t)
  rw [sub_add_sub_cancel] at hn
  linarith

/-- Concatenates two explicit coordinate attachments and a net connection.
Every traversal is charged and every vertex is retained in the tube. -/
theorem localTravel_attach (μ : Plane → ℝ) (w : Edge → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q p' q' : Vertex) (r a η δ s : ℝ)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r)
    (hleft : pathCost w p (coordinatePath p p') ≤ a)
    (hright : pathCost w q' (coordinatePath q' q) ≤ a)
    (hmid : LocalTravel μ η δ s p' q' w) :
    ∃ ds, p+displacement ds=q ∧
        pathCost w p ds ≤ μ (latticeEmbed (q-p))+η*s+2*a+2*β*r ∧
        PathIn p ds (SegmentTube p q (max (3*r) (δ*s+r))) := by
  obtain ⟨ds,hd,hcost,hin⟩ := hmid
  let l := coordinatePath p p'
  let v := coordinatePath q' q
  have hl : p+displacement l=p' := coordinatePath_endpoint p p'
  have hv : q'+displacement v=q := coordinatePath_endpoint q' q
  have hμdiff : μ (latticeEmbed (q'-p')) ≤ μ (latticeEmbed (q-p))+2*β*r := by
    have he : latticeEmbed (q'-p')-latticeEmbed (q-p) =
        latticeEmbed (q'-q)-latticeEmbed (p'-p) := by
      simp only [latticeEmbed_sub]; abel
    have hn : ‖latticeEmbed (q'-p')-latticeEmbed (q-p)‖ ≤ 2*r := by
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith)
    have ht := (le_abs_self _).trans (hlip (latticeEmbed (q'-p')) (latticeEmbed (q-p)))
    have hb := mul_le_mul_of_nonneg_left hn hβ
    linarith
  have hll : PathIn p l (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i _
    refine ⟨0,by norm_num,by norm_num,?_⟩
    have hb := coordinatePath_prefix_bound p p' i
    have hdist := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hdist
    have hr : 0 ≤ r := (norm_nonneg _).trans hp
    simp only [segmentPoint,zero_smul,add_zero]
    rw [← latticeEmbed_sub]
    exact hb.trans ((hdist.trans (by linarith)).trans (le_max_left _ _))
  have hrr : PathIn q' v (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i _
    refine ⟨1,by norm_num,by norm_num,?_⟩
    have hb := coordinatePath_prefix_bound q' q i
    have hdist := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hdist
    have hn := norm_add_le
      (latticeEmbed (q'+displacement (v.take i))-latticeEmbed q')
      (latticeEmbed q'-latticeEmbed q)
    rw [sub_add_sub_cancel,← latticeEmbed_sub,← latticeEmbed_sub,← latticeEmbed_sub] at hn
    simp only [segmentPoint,one_smul,add_sub_cancel]
    rw [← latticeEmbed_sub]
    exact (hn.trans (by dsimp [v] at *; linarith)).trans (le_max_left _ _)
  have hmm : PathIn p' ds (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i hi
    obtain ⟨t,ht0,ht1,ht⟩ := segmentTube_perturbation p q p' q' r (δ*s) hp hq (hin i hi)
    exact ⟨t,ht0,ht1,ht.trans (le_max_right _ _)⟩
  refine ⟨l++ds++v,?_,?_,?_⟩
  · rw [displacement_append,displacement_append,← add_assoc,← add_assoc,hl,hd,hv]
  · rw [pathCost_append,pathCost_append,displacement_append,← add_assoc,hl,hd]
    dsimp [l,v]
    linarith
  · apply pathIn_append _ _ _ _ (pathIn_append _ _ _ _ hll (by simpa [hl] using hmm))
    simpa only [displacement_append,← add_assoc,hl,hd] using hrr

/-- A fixed finite Euclidean net; its cardinality is independent of scale. -/
theorem finite_ball_net (D γ : ℝ) (hγ : 0 < γ) :
    ∃ S : Finset {v : Plane // ‖v‖ ≤ D},
      ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ := by
  classical
  have hc : closedBall (0 : Plane) D ⊆
      ⋃ u : {v : Plane // ‖v‖ ≤ D}, ball u.val γ := by
    intro v hv
    have hv' : ‖v‖ ≤ D := by simpa using hv
    exact mem_iUnion.mpr ⟨⟨v,hv'⟩,by simpa using hγ⟩
  obtain ⟨S,hS⟩ := (isCompact_closedBall (0 : Plane) D).elim_finite_subcover
    (fun u : {v : Plane // ‖v‖ ≤ D} => ball u.val γ) (fun _ => isOpen_ball) hc
  refine ⟨S,?_⟩
  intro v hv
  obtain ⟨u,hu,hvu⟩ := mem_iUnion₂.mp (hS (by simpa using hv))
  exact ⟨u,hu,hvu⟩

theorem lattice_mem_box_of_norm (p : Vertex) (n : ℕ)
    (hp : ‖latticeEmbed p‖ ≤ (n : ℝ)) : p ∈ latticeBox n := by
  have h0 := (plane_coordinate_le_norm (latticeEmbed p) 0).trans hp
  have h1 := (plane_coordinate_le_norm (latticeEmbed p) 1).trans hp
  simp only [latticeEmbed,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have hh0 : -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n := by exact_mod_cast abs_le.mp h0
  have hh1 : -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n := by exact_mod_cast abs_le.mp h1
  simpa only [latticeBox,Finset.mem_product,Finset.mem_Icc] using And.intro hh0 hh1

theorem scaled_net_norm (D : ℝ) (u : {v : Plane // ‖v‖ ≤ D}) (n : ℕ) :
    ‖latticeEmbed (latticeFloor ((n : ℝ) • u.val))‖ ≤ D*n+2 := by
  have ht := norm_add_le
    (latticeEmbed (latticeFloor ((n : ℝ) • u.val))-(n : ℝ) • u.val)
    ((n : ℝ) • u.val)
  rw [sub_add_cancel,norm_smul,Real.norm_natCast] at ht
  have hu := mul_le_mul_of_nonneg_left u.property (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith [latticeFloor_error ((n : ℝ) • u.val)]

theorem scaled_net_approximates (D γ : ℝ)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (n : ℕ) (hn : 0 < n) (p : Vertex) (hp : ‖latticeEmbed p‖ ≤ D*n) :
    ∃ u ∈ S, ‖latticeEmbed (latticeFloor ((n : ℝ) • u.val)-p)‖ ≤ γ*n+2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let v := (1/(n : ℝ)) • latticeEmbed p
  have hv : ‖v‖ ≤ D := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hn')]
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ hn').mpr (by nlinarith)
  obtain ⟨u,hu,hvu⟩ := hS v hv
  refine ⟨u,hu,?_⟩
  have he : (n : ℝ) • v = latticeEmbed p := by
    dsimp [v]; rw [smul_smul]; simp [hn'.ne']
  have hd : ‖(n : ℝ) • u.val-latticeEmbed p‖ ≤ γ*n := by
    rw [← he,← smul_sub,norm_smul,Real.norm_natCast,norm_sub_rev]
    nlinarith
  have ht := norm_add_le
    (latticeEmbed (latticeFloor ((n : ℝ) • u.val))-(n : ℝ) • u.val)
    ((n : ℝ) • u.val-latticeEmbed p)
  rw [sub_add_sub_cancel,← latticeEmbed_sub] at ht
  linarith [latticeFloor_error ((n : ℝ) • u.val)]

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BallTravelGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

theorem ballTravel_of_net (μ : Plane → ℝ) (w : Edge → ℝ)
    (D γ β η δ κ A : ℝ) (hA : 0 < A) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (C n : ℕ) (hn : 0 < n) (hbox : D*n+2 ≤ (C*n : ℕ))
    (hcost : η/4*n+2*((2*A)*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n)
    (htube : max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n)
    (hc : ∀ p ∈ latticeBox (C*n), ∀ q ∈ latticeBox (C*n),
      pathCost w p (coordinatePath p q) < A*(latticeDistance p q : ℝ)+κ*(C*n : ℕ))
    (hm : ∀ u ∈ S, ∀ v ∈ S, LocalTravel μ (η/4) (δ/2) n
      (latticeFloor ((n : ℝ) • u.val)) (latticeFloor ((n : ℝ) • v.val)) w) :
    BallTravel μ D η δ n w := by
  intro p q hp hq
  obtain ⟨u,hu,hpu⟩ := scaled_net_approximates D γ S hS n hn p hp
  obtain ⟨v,hv,hqv⟩ := scaled_net_approximates D γ S hS n hn q hq
  let p' := latticeFloor ((n : ℝ) • u.val)
  let q' := latticeFloor ((n : ℝ) • v.val)
  have hpbox : p ∈ latticeBox (C*n) := lattice_mem_box_of_norm p (C*n) (hp.trans (by linarith))
  have hqbox : q ∈ latticeBox (C*n) := lattice_mem_box_of_norm q (C*n) (hq.trans (by linarith))
  have hp'box : p' ∈ latticeBox (C*n) := lattice_mem_box_of_norm p' (C*n)
    ((scaled_net_norm D u n).trans hbox)
  have hq'box : q' ∈ latticeBox (C*n) := lattice_mem_box_of_norm q' (C*n)
    ((scaled_net_norm D v n).trans hbox)
  have hleft : pathCost w p (coordinatePath p p') ≤ (2*A)*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hd
    have hh := hc p hpbox p' hp'box
    dsimp [p'] at *
    have hd' := mul_le_mul_of_nonneg_left hd hA.le
    have hp' := mul_le_mul_of_nonneg_left hpu hA.le
    nlinarith
  have hright : pathCost w q' (coordinatePath q' q) ≤ (2*A)*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hd
    have hh := hc q' hq'box q hqbox
    dsimp [q'] at *
    have hd' := mul_le_mul_of_nonneg_left hd hA.le
    have hq' := mul_le_mul_of_nonneg_left hqv hA.le
    nlinarith
  obtain ⟨ds,hend,hc',ht'⟩ := localTravel_attach μ w β hβ hlip p q p' q'
    (γ*n+2) ((2*A)*(γ*n+2)+κ*(C*n : ℕ)) (η/4) (δ/2) n hpu hqv hleft hright (hm u hu v hv)
  refine ⟨ds,hend,hc'.trans (by linarith),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := ht' i hi
  exact ⟨t,ht0,ht1,hbound.trans htube⟩

theorem ballTravel_parameters (D β η δ A : ℝ)
    (hA : 0 < A)
    (hD : 0 < D) (hβ : 0 ≤ β) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ γ κ : ℝ, ∃ C : ℕ, 0 < γ ∧ 0 < κ ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        0 < n ∧ D*n+2 ≤ (C*n : ℕ) ∧
        η/4*n+2*((2*A)*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n ∧
        max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n := by
  obtain ⟨C,hC⟩ := exists_nat_gt (D+2)
  have hc : (0 : ℝ) < C := by linarith
  have hc' : 0 < C := by exact_mod_cast hc
  let γ := min (η/(8*(4*A+2*β))) (δ/12)
  let κ := η/(16*(C : ℝ))
  have hγ : 0 < γ := lt_min (div_pos hη (by positivity)) (by positivity)
  have hκ : 0 < κ := div_pos hη (by positivity)
  have hgη : (4*A+2*β)*γ ≤ η/8 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 8*(4*A+2*β))).mp (min_le_left _ _ : γ ≤ _)
    nlinarith
  have hgδ : γ ≤ δ/12 := min_le_right _ _
  have hk : κ*(C : ℝ)=η/16 := by dsimp [κ]; field_simp
  refine ⟨γ,κ,C,hγ,hκ,hc',?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (4*(8*A+4*β)/η)),
    hlim.eventually (eventually_ge_atTop (24/δ))] with n hn hnη hnδ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hhη := (div_le_iff₀ hη).mp hnη
  have hhδ := (div_le_iff₀ hδ).mp hnδ
  have hge := mul_le_mul_of_nonneg_right hgη hn0
  have hgd := mul_le_mul_of_nonneg_right hgδ hn0
  have hcb := mul_le_mul_of_nonneg_right hC.le hn0
  simp only [Nat.cast_mul]
  refine ⟨by omega,by nlinarith,?_,?_⟩
  · have he : κ*((C : ℝ)*n)=(η/16)*n := by rw [← mul_assoc,hk]
    rw [he]
    nlinarith
  · apply max_le <;> nlinarith

theorem localTravel_mono (μ : Plane → ℝ) (w : Edge → ℝ) (p q : Vertex)
    {η δ s η' δ' s' : ℝ} (hη : η*s ≤ η'*s') (hδ : δ*s ≤ δ'*s')
    (h : LocalTravel μ η δ s p q w) : LocalTravel μ η' δ' s' p q w := by
  obtain ⟨ds,hend,hcost,htube⟩ := h
  refine ⟨ds,hend,hcost.trans (add_le_add le_rfl hη),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := htube i hi
  exact ⟨t,ht0,ht1,hbound.trans hδ⟩

theorem measurableSet_localTravel (μ : Plane → ℝ) (η δ s : ℝ) (p q : Vertex) :
    MeasurableSet {w | LocalTravel μ η δ s p q w} := by
  have hm := measurableSet_bounded_path_event (τ := fun e (w : Edge → ℝ) => w e)
    measurable_pi_apply
    (fun x ds => x=p ∧ x+displacement ds=q ∧ PathIn x ds (SegmentTube p q (δ*s)))
    (fun _ _ => μ (latticeEmbed (q-p))+η*s)
  convert hm using 1
  ext w
  constructor
  · rintro ⟨ds,hend,hcost,htube⟩
    exact ⟨p,ds,⟨rfl,hend,htube⟩,hcost⟩
  · rintro ⟨x,ds,⟨rfl,hend,htube⟩,hcost⟩
    exact ⟨ds,hend,hcost,htube⟩

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BallTravel
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem gamma_badConnections_tendsto_zero
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun n => P.real (gammaBadConnections shape rate τ κ n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (h.gammaBadConnections_probability hs hr κ)
  exact (summable_gamma_box_connection_bound hr hκ).tendsto_atTop_zero

theorem gamma_ball_travel_nat (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)})
      atTop (𝓝 0) := by
  classical
  let μ := gammaMeanNorm h hs hr
  have hμ := gammaMeanNorm_laws h hs hr
  let _ := h.probability
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  obtain ⟨γ,κ,C,hγ,hκ,hC,hparams⟩ := ballTravel_parameters D β η δ (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr) hD hβ.le hη hδ
  obtain ⟨S,hS⟩ := finite_ball_net D γ hγ
  let A (n : ℕ) := ⋃ uv ∈ S ×ˢ S, {ω | ¬LocalTravel μ (η/4) (δ/2) n
    (latticeFloor ((n : ℝ) • uv.1.val)) (latticeFloor ((n : ℝ) • uv.2.val)) (fun e => τ e ω)}
  have hA : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
    apply (tendsto_order.2 ⟨?_,?_⟩)
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
    · intro ε hε
      have hden : 0 < ((S ×ˢ S).card : ℝ)+1 := by positivity
      filter_upwards [eventually_ge_atTop 1,
        gamma_tube_travel_nat h hs hr (2*D+4) (η/4) (δ/2)
          (by linarith) (by linarith) (by linarith)
          (ε/(((S ×ˢ S).card : ℝ)+1)) (div_pos hε hden)] with n hn hh
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hbound : P.real (A n) ≤ ((S ×ˢ S).card : ℝ)*(ε/(((S ×ˢ S).card : ℝ)+1)) := by
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        calc
          _ ≤ ∑ _uv ∈ S ×ˢ S, ε/(((S ×ˢ S).card : ℝ)+1) := by
            apply sum_le_sum
            intro uv huv
            apply (hh _ _ ?_).le
            rw [latticeEmbed_sub]
            exact (norm_sub_le _ _).trans (by
              have h1 := scaled_net_norm D uv.1 n
              have h2 := scaled_net_norm D uv.2 n
              nlinarith)
          _ = _ := by simp
      apply hbound.trans_lt
      have he := (div_pos hε hden)
      have hid : ((((S ×ˢ S).card : ℝ)+1))*(ε/(((S ×ˢ S).card : ℝ)+1))=ε := by field_simp
      nlinarith
  have hCn : Tendsto (fun n : ℕ => C*n) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_left n hC)
  have hB := (gamma_badConnections_tendsto_zero h hs hr κ hκ).comp hCn
  have hbound : ∀ᶠ n : ℕ in atTop,
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)} ≤
        P.real (gammaBadConnections shape rate τ κ (C*n))+P.real (A n) := by
    filter_upwards [hparams] with n hn
    have hsub : {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ n (fun e => τ e ω)} ⊆
        gammaBadConnections shape rate τ κ (C*n) ∪ A n := by
      intro ω hω
      by_contra hb
      have hc : ω ∉ gammaBadConnections shape rate τ κ (C*n) := fun hc => hb (Or.inl hc)
      have hm : ω ∉ A n := fun hm => hb (Or.inr hm)
      apply hω
      apply ballTravel_of_net μ _ D γ β η δ κ (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr) hβ.le hlip S hS C n
        hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
      · intro p hp q hq
        by_contra hh
        exact hc (mem_iUnion₂.mpr ⟨(p,q),mem_product.mpr ⟨hp,hq⟩,le_of_not_gt hh⟩)
      · intro u hu v hv
        by_contra hh
        exact hm (mem_iUnion₂.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,hh⟩)
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) hbound
    (by simpa using hB.add hA)

theorem measurableSet_ballTravel (μ : Plane → ℝ) (D η δ s : ℝ) :
    MeasurableSet {w | BallTravel μ D η δ s w} := by
  simp only [BallTravel,ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun q =>
    MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_localTravel μ η δ s p q))))

theorem gamma_ball_travel (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ a : Vertex,
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ (shiftEdge a e) ω)} < ε := by
  let _ := h.probability
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((gamma_ball_travel_nat h hs hr D (η/2) (δ/2) hD (by linarith) (by linarith)).eventually
      (gt_mem_nhds hε))
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with s hscale
  intro a
  have he := h.translated_event_probability a
    {w | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s w} (measurableSet_ballTravel (gammaMeanNorm h hs hr) D η δ s).compl
  rw [show P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ (shiftEdge a e) ω)} =
      P.real {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ e ω)} from congrArg ENNReal.toReal he]
  let n : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hscale
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  have hnN : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hscale).trans hsn
  have hnupper : (n : ℝ) ≤ 2*s := by
    have hh : (n : ℝ) < s+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hη' : (η/2)*(n : ℝ) ≤ η*s := by nlinarith
  have hδ' : (δ/2)*(n : ℝ) ≤ δ*s := by nlinarith
  refine (measureReal_mono (show {ω | ¬BallTravel (gammaMeanNorm h hs hr) D η δ s (fun e => τ e ω)} ⊆
      {ω | ¬BallTravel (gammaMeanNorm h hs hr) D (η/2) (δ/2) n (fun e => τ e ω)} from ?_)).trans_lt (hN n hnN)
  intro ω hb hg
  apply hb
  intro p q hp hq
  apply localTravel_mono (gammaMeanNorm h hs hr) _ p q hη' hδ'
  apply hg p q <;> nlinarith

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RecordScales
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic characteristic record scales (Lemma `gr:record-scales`)
from positivity and a cubic upper bound. -/
namespace GammaFPP.CrossingBridge
open Filter
open scoped Topology

/-- A positive null sequence has a strict record minimum after every index. -/
theorem exists_strict_record_after (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k)
    (hlim : Tendsto a atTop (𝓝 0)) (N : ℕ) :
    ∃ k, N < k ∧ ∀ i < k, a k < a i := by
  classical
  obtain ⟨i, hi, hmin⟩ := (Finset.range (N + 1)).exists_min_image a (by simp)
  have hex : ∃ k, a k < a i := (hlim.eventually (gt_mem_nhds (hpos i))).exists
  refine ⟨Nat.find hex, ?_, ?_⟩
  · by_contra h
    have hk : Nat.find hex ∈ Finset.range (N + 1) := by
      simp only [Finset.mem_range]
      omega
    exact (not_lt_of_ge (hmin _ hk)) (Nat.find_spec hex)
  · intro j hj
    have hj' : a i ≤ a j := le_of_not_gt (Nat.find_min hex hj)
    exact lt_of_lt_of_le (Nat.find_spec hex) hj'

/-- Normalizing the characteristic lengths by 16^k makes them a null sequence. -/
theorem normalized_lengths_tendsto (L : ℕ → ℝ)
    (hpos : ∀ k, 0 < L k) (hbound : ∀ k, L k ≤ (2 : ℝ) ^ (3 * k)) :
    Tendsto (fun k => L k * (1 / 16 : ℝ) ^ k) atTop (𝓝 0) := by
  have hupper : ∀ k, L k * (1 / 16 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    calc
      L k * (1 / 16 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k) * (1 / 16 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (hbound k) (by positivity)
      _ = (1 / 2 : ℝ) ^ k := by
        rw [pow_mul, ← mul_pow]
        norm_num
  exact squeeze_zero (fun k => mul_nonneg (hpos k).le (by positivity)) hupper
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- Record-scale comparison in denominator-free form:
`L_k ≤ 16^(k-i) L_i` for every previous index `i`. -/
theorem record_scales (L : ℕ → ℝ) (hpos : ∀ k, 0 < L k)
    (hbound : ∀ k, L k ≤ (2 : ℝ) ^ (3 * k)) :
    ∀ N, ∃ k, N < k ∧ ∀ i ≤ k, L k ≤ (16 : ℝ) ^ (k - i) * L i := by
  intro N
  obtain ⟨k, hk, hrec⟩ := exists_strict_record_after
    (fun k => L k * (1 / 16 : ℝ) ^ k) (fun k => mul_pos (hpos k) (by positivity))
    (normalized_lengths_tendsto L hpos hbound) N
  refine ⟨k, hk, ?_⟩
  intro i hi
  have hcmp : L k * (1 / 16 : ℝ) ^ k ≤ L i * (1 / 16 : ℝ) ^ i := by
    rcases eq_or_lt_of_le hi with rfl | hi
    · exact le_refl _
    · exact le_of_lt (hrec i hi)
  have hp : (0 : ℝ) < 16 ^ k := by positivity
  have hmult := mul_le_mul_of_nonneg_right hcmp (le_of_lt hp)
  have hki : k = i + (k - i) := by omega
  have heq : (1 / 16 : ℝ) ^ i * 16 ^ k = 16 ^ (k - i) := by
    conv_lhs => rw [hki, pow_add]
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have hone : (1 / 16 : ℝ) ^ k * 16 ^ k = 1 := by
    rw [← mul_pow]; norm_num
  calc
    L k = (L k * (1 / 16 : ℝ) ^ k) * 16 ^ k := by rw [mul_assoc, hone, mul_one]
    _ ≤ (L i * (1 / 16 : ℝ) ^ i) * 16 ^ k := hmult
    _ = 16 ^ (k - i) * L i := by rw [mul_assoc, heq, mul_comm]

/-- Record-scale comparison from an initial index `k₀`, using `k-j` and
requiring no bound below `k₀`. -/
theorem record_scales_from (L : ℕ → ℝ) (k₀ : ℕ)
    (hpos : ∀ k, k₀ ≤ k → 0 < L k)
    (hbound : ∀ k, k₀ ≤ k → L k ≤ (2 : ℝ) ^ (3 * k)) :
    ∀ N, ∃ k, N < k ∧ k₀ ≤ k ∧
      ∀ j, j ≤ k - k₀ → (1 / 16 : ℝ) ^ j * L k ≤ L (k - j) := by
  classical
  intro N
  let L' : ℕ → ℝ := fun k => if k₀ ≤ k then L k else 1
  have hp : ∀ k, 0 < L' k := by
    intro k
    dsimp [L']
    split_ifs with h
    · exact hpos k h
    · norm_num
  have hb : ∀ k, L' k ≤ (2 : ℝ) ^ (3 * k) := by
    intro k
    dsimp [L']
    split_ifs with h
    · exact hbound k h
    · exact one_le_pow₀ (by norm_num)
  obtain ⟨k, hk, hrec⟩ := record_scales L' hp hb (max N k₀)
  have hk₀ : k₀ ≤ k := by omega
  refine ⟨k, by omega, hk₀, ?_⟩
  intro j hj
  have hjk : j ≤ k := by omega
  have hk' : k₀ ≤ k - j := by omega
  have hcomp := hrec (k - j) (Nat.sub_le _ _)
  have hsub : k - (k - j) = j := by omega
  simp only [L', ite_eq_left hk₀, ite_eq_left hk', hsub] at hcomp
  have hm := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ (1 / 16 : ℝ) ^ j by positivity)
  have hcancel : (1 / 16 : ℝ) ^ j * 16 ^ j = 1 := by
    rw [← mul_pow]; norm_num
  simpa only [← mul_assoc, hcancel, one_mul] using hm

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RareFastEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

theorem mem_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ rareFastEvent b m a A R ε s n t ↔
      ∃ p ds, p.1=t.1 ∧ (p+displacement ds).1=t.1+n ∧
        PathIn p ds (rareFastRegion b A R s n t) ∧ defect w b m a p ds < -ε*s := by
  simp only [rareFastEvent,strictLocalizedEvent,mem_ofPred_eq,defect]
  have hV : (rareFastVertices b A R s n t : Set Vertex)=rareFastRegion b A R s n t := by
    ext p; simp
  rw [hV]
  constructor
  · rintro ⟨p,ds,⟨hp,hq⟩,hin,hc⟩
    exact ⟨p,ds,hp,hq,hin,by linarith⟩
  · rintro ⟨p,ds,hp,hq,hin,hc⟩
    exact ⟨p,ds,⟨hp,hq⟩,hin,by linarith⟩

theorem measurableSet_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    MeasurableSet (rareFastEvent b m a A R ε s n t) :=
  measurableSet_strictLocalizedEvent _ _ _

/-- Translating weights is exactly equivalent to translating all path vertices;
the supporting functional is evaluated on the unchanged displacement. -/
theorem rareFastEvent_translate (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    (fun e => w (shiftEdge t e)) ∈ rareFastEvent b m a A R ε s n 0 ↔
      w ∈ rareFastEvent b m a A R ε s n t := by
  rw [mem_rareFastEvent,mem_rareFastEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m a p ds =
      defect w b m a (t+p) ds := by simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨t+p,ds,by simpa using hp,by simpa [add_assoc] using hq,?_,?_⟩
    · intro i hi
      have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
      change _ ∈ rareFastRegion b A R s n t
      simpa only [rareFastRegion,mem_ofPred_eq,he,sub_zero] using hin i hi
    · rwa [← hc]
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨p-t,ds,by simpa using sub_eq_zero.mpr hp,?_,?_,?_⟩
    · simp only [Prod.fst_add,Prod.fst_sub,Prod.fst_zero] at *
      omega
    · intro i hi
      have he : p-t+displacement (ds.take i)=(p+displacement (ds.take i))-t := by abel
      rw [he]
      simpa [rareFastRegion] using hin i hi
    · have he : t + (p-t) = p := by abel
      rw [hc,he]
      exact hcost

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

theorem rareFastEvent_probability_translate (h : GammaEnvironment shape rate P τ)
    (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} =
      P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0} := by
  have he : {ω | (fun e => τ (shiftEdge t e) ω) ∈ rareFastEvent b m a A R ε s n 0} =
      {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} := by
    ext ω
    exact rareFastEvent_translate b m a A R ε s n t (fun e => τ e ω)
  rw [← he]
  exact h.translated_event_probability t _ (measurableSet_rareFastEvent ..)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConnectorGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set

theorem transverse_plane_lipschitz (b : ℝ) (hb : |b| ≤ 1) (z : Plane) :
    |rCoord b z| ≤ 2*‖z‖ := by
  have hh := abs_sub_le (z 1) 0 (b*z 0)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at hh
  have hc₀ := plane_coordinate_le_norm z 0
  have hc₁ := plane_coordinate_le_norm z 1
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (z 0))
  change |z 1-b*z 0| ≤ _
  nlinarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Grid
open PlanarFPP Finset

lemma verticalIntervalEdges_card (X lo hi : ℤ) :
    (verticalIntervalEdges X lo hi).card=(hi-lo).toNat := by
  rw [verticalIntervalEdges,Finset.card_image_of_injective]
  · exact Int.card_Ico lo hi
  · intro a b hab
    exact congrArg (fun e : Edge => e.1.2) hab

lemma transverseIntervalEdges_card_le (b : ℝ) (X : ℤ) (lo hi A : ℝ)
    (hA : 0 ≤ A) (hwidth : hi-lo ≤ A) :
    ((transverseIntervalEdges b X lo hi).card : ℝ) ≤ A := by
  rw [transverseIntervalEdges,verticalIntervalEdges_card]
  by_cases hle : ⌈lo+b*X⌉ ≤ ⌊hi+b*X⌋
  · have he : ((⌊hi+b*X⌋-⌈lo+b*X⌉).toNat : ℝ) = (⌊hi+b*X⌋ : ℝ)-(⌈lo+b*X⌉ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ ⌊hi+b*X⌋-⌈lo+b*X⌉ by omega)
    rw [he]
    have hl := Int.le_ceil (lo+b*X)
    have hh := Int.floor_le (hi+b*X)
    linarith
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    simpa using hA

lemma grid_interval_card (b : ℝ) (X h w : ℤ) (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w) :
    ((transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w)).card : ℝ) ≤
      50*(j : ℝ)^2*w := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj2 : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hj2 (show 0 ≤ (w : ℝ) by linarith)
  apply transverseIntervalEdges_card_le _ _ _ _ _ (by positivity)
  unfold gridIntervalLower gridIntervalUpper
  nlinarith

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Grid
open PlanarFPP MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

lemma verticalExponent_pos {shape : ℝ} (hs : 0 < shape) : 0 < verticalExponent shape := by
  have hl : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at h
    exact h
  unfold verticalExponent
  positivity

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Exponential cost tail for an edge set of cardinality at most `50*L`. -/
theorem vertical_edgeSet_tail (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset Edge) (L : ℝ)
    (hcard : (S.card : ℝ) ≤ 50 * L) :
    P.real {ω | 100 * shape / rate * L < edgeSum S τ ω} ≤
      Real.exp (-verticalExponent shape * L) := by
  let _ := h.probability
  have hp : 0 < rate / 2 := by positivity
  have hl : rate / 2 < rate := by linarith
  have he : rate / (rate - rate / 2) = 2 := by
    field_simp [hr.ne']
    ring
  have hb := h.upper_tail_edgeSum hs hr hp hl S (100 * shape / rate * L)
  rw [he] at hb
  have hbase : 0 ≤ (2 : ℝ) ^ shape := (Real.rpow_pos_of_pos (by norm_num) shape).le
  have hden : ENNReal.ofReal (Real.exp ((rate / 2) * (100 * shape / rate * L))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfinite : (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ S.card /
      ENNReal.ofReal (Real.exp ((rate / 2) * (100 * shape / rate * L))) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden
  have hreal := ENNReal.toReal_mono hfinite hb
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  change P.real _ ≤ _ at hreal
  have hsub : {ω | 100 * shape / rate * L < edgeSum S τ ω} ⊆
      {ω | 100 * shape / rate * L ≤ edgeSum S τ ω} := by
    intro ω hω
    change 100 * shape / rate * L < edgeSum S τ ω at hω
    change 100 * shape / rate * L ≤ edgeSum S τ ω
    exact hω.le
  refine (measureReal_mono (μ := P) hsub (measure_ne_top P _)).trans (hreal.trans ?_)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul,
    ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hcard (mul_nonneg hlog hs.le)
  have hc : rate / 2 * (100 * shape / rate * L) = 50 * shape * L := by
    field_simp [hr.ne']
    ring
  rw [hc]
  unfold verticalExponent
  nlinarith

/-- Failure bound from disjoint crossing trials and Gamma attachment tails. -/
theorem bin_failure_bound (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) {ι : Type*}
    (trials : Finset ι) (A : ι → Set (Edge → ℝ)) (supports : ι → Finset Edge)
    (hA : ∀ i ∈ trials, MeasurableSet (A i))
    (hdep : ∀ i ∈ trials, DependsOnEdges (A i) (supports i))
    (hdis : Set.Pairwise (↑trials : Set ι) (fun i j => Disjoint (supports i) (supports j)))
    (q : ℝ) (hq : ∀ i ∈ trials, q ≤ P.real {ω | (fun e => τ e ω) ∈ A i})
    (S₁ S₂ : Finset Edge) (L : ℝ)
    (hc₁ : (S₁.card : ℝ) ≤ 50 * L) (hc₂ : (S₂.card : ℝ) ≤ 50 * L) :
    P.real {ω | (fun e => τ e ω) ∉ binGood trials A S₁ S₂ shape rate L} ≤
      (1-q)^trials.card + 2 * Real.exp (-verticalExponent shape * L) := by
  let _ := h.probability
  let F := {ω | ∀ i ∈ trials, (fun e => τ e ω) ∉ A i}
  let V₁ := {ω | 100 * shape / rate * L < edgeSum S₁ τ ω}
  let V₂ := {ω | 100 * shape / rate * L < edgeSum S₂ τ ω}
  have hsub : {ω | (fun e => τ e ω) ∉ binGood trials A S₁ S₂ shape rate L} ⊆ F ∪ V₁ ∪ V₂ := by
    intro ω hω
    simp only [binGood, Set.mem_ofPred_eq, not_and_or, not_exists, not_le] at hω
    rcases hω with hf | hv | hv
    · apply Or.inl
      apply Or.inl
      change ∀ i ∈ trials, (fun e => τ e ω) ∉ A i
      intro i hi
      exact (hf i).resolve_left (not_not.mpr hi)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  have hf := disjoint_trials_failure_bound h trials A supports hA hdep hdis q hq
  have hv₁ := vertical_edgeSet_tail h hs hr S₁ L hc₁
  have hv₂ := vertical_edgeSet_tail h hs hr S₂ L hc₂
  have hh := (measureReal_mono (μ := P) hsub).trans
    ((measureReal_union_le (μ := P) (F ∪ V₁) V₂).trans
      (add_le_add (measureReal_union_le (μ := P) F V₁) le_rfl))
  change P.real F ≤ _ at hf
  change P.real V₁ ≤ _ at hv₁
  change P.real V₂ ≤ _ at hv₂
  linarith

/-- Failure bound for `j²` separated translated trials and the left and right
vertical attachment intervals. -/
theorem source_bin_failure_bound (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (b : ℝ) (X h w l : ℤ)
    (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w)
    (A : Fin (j^2) → Set (Edge → ℝ)) (supports : Fin (j^2) → Finset Edge)
    (hA : ∀ i, MeasurableSet (A i))
    (hdep : ∀ i, DependsOnEdges (A i) (supports i))
    (hdis : Pairwise (fun i k => Disjoint (supports i) (supports k)))
    (q : ℝ) (hq : ∀ i, q ≤ P.real {ω | (fun e => τ e ω) ∈ A i}) :
    P.real {ω | (fun e => τ e ω) ∉ binGood Finset.univ A
      (transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w))
      (transverseIntervalEdges b (X+l) (gridIntervalLower h w) (gridIntervalUpper j h w))
      shape rate ((j : ℝ)^2*w)} ≤
        (1-q)^(j^2)+2*Real.exp (-verticalExponent shape*(j : ℝ)^2*w) := by
  have hb := bin_failure_bound henv hs hr Finset.univ A supports
    (fun i _ => hA i) (fun i _ => hdep i) (fun i _ k _ hik => hdis hik) q
    (fun i _ => hq i)
    (transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w))
    (transverseIntervalEdges b (X+l) (gridIntervalLower h w) (gridIntervalUpper j h w))
    ((j : ℝ)^2*w)
    (by simpa only [mul_assoc] using grid_interval_card b X h w j hj hw)
    (by simpa only [mul_assoc] using grid_interval_card b (X+l) h w j hj hw)
  simpa only [Finset.card_univ, Fintype.card_fin, mul_assoc] using hb

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

theorem measurableSet_crossingEvent (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    MeasurableSet (crossingEvent b m K s n t) := measurableSet_strictLocalizedEvent _ _ _

theorem crossingEvent_depends (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    DependsOnEdges (crossingEvent b m K s n t) (internalEdges (rareFastVertices b 1 8 s n t)) :=
  strictLocalizedEvent_depends _ _ _

lemma crossingEvent_eq_rareFastEvent (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    crossingEvent b m K s n t = rareFastEvent b m 0 1 8 (-K) s n t := by
  ext w
  constructor <;> rintro ⟨p,ds,hcols,hin,hcost⟩
  all_goals
    have hd : (displacement ds).1=n := by
      have hh := hcols.2
      simp only [Prod.fst_add,hcols.1] at hh
      omega
    refine ⟨p,ds,hcols,hin,?_⟩
    simpa only [support,zero_mul,add_zero,hd,neg_mul,sub_neg_eq_add] using hcost

lemma gridTrialTranslate_center (b : ℝ) (X h w : ℤ) (t : ℕ) :
    transverse b (gridTrialTranslate b X h w t) =
      (⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(t+1))*w := by
  simp [gridTrialTranslate,transverse]
  ring

lemma gridTrialTranslate_separation (b : ℝ) (X h w : ℤ) (hw : 1 ≤ w)
    {t u : ℕ} (htu : t ≠ u) :
    2*(8*(w : ℝ)) < |transverse b (gridTrialTranslate b X h w t)-
      transverse b (gridTrialTranslate b X h w u)| := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hsep : 1 ≤ |(t : ℝ)-u| := by
    have hn : (1 : ℤ) ≤ |(t : ℤ)-u| := by
      rw [abs_eq_max_neg]
      omega
    exact_mod_cast hn
  rw [gridTrialTranslate_center,gridTrialTranslate_center,
    show ((⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(t+1))*w)-
      ((⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(u+1))*w) =
      30*(w : ℝ)*((t : ℝ)-u) by ring,abs_mul,abs_of_nonneg (by positivity)]
  nlinarith

lemma gridTrials_disjoint (b : ℝ) (X h w l : ℤ) (hw : 1 ≤ w) (j : ℕ) :
    Pairwise (fun t u : Fin (j^2) => Disjoint
      (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w t))
      (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w u))) := by
  intro t u htu
  apply strip_vertices_disjoint _ _ b
    (transverse b (gridTrialTranslate b X h w t))
    (transverse b (gridTrialTranslate b X h w u)) (8*w)
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · exact gridTrialTranslate_separation b X h w hw (fun he => htu (Fin.ext he))

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma crossingEvent_probability_translate (h : GammaEnvironment shape rate P τ)
    (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n t} =
      P {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} := by
  simp only [crossingEvent_eq_rareFastEvent]
  exact rareFastEvent_probability_translate h b m 0 1 8 (-K) s n t

theorem gridBinGood_failure_bound (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (b m K q₀ : ℝ)
    (X h w l : ℤ) (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w)
    (hq : q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m K w l 0}) :
    P.real {ω | (fun e => τ e ω) ∉ gridBinGood shape rate b m K X h w l j} ≤
      (1-q₀)^(j^2)+2*Real.exp (-Grid.verticalExponent shape*(j : ℝ)^2*w) := by
  refine Grid.source_bin_failure_bound henv hs hr b X h w l j hj hw
    (fun t => crossingEvent b m K w l (gridTrialTranslate b X h w t))
    (fun t => internalEdges (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w t)))
    ?_ ?_ ?_ q₀ ?_
  · intro t
    exact measurableSet_crossingEvent ..
  · intro t
    exact crossingEvent_depends b m K w l (gridTrialTranslate b X h w t)
  · intro t u htu
    exact internalEdges_disjoint (gridTrials_disjoint b X h w l hw j htu)
  · intro t
    unfold Measure.real
    rw [crossingEvent_probability_translate henv]
    exact hq

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SourceTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem sourceCrossingK_ge_hundred (shape rate : ℝ) (μ : Plane → ℝ) (b : ℝ) :
    100 ≤ sourceCrossingK shape rate μ b := by
  unfold sourceCrossingK
  nlinarith [abs_nonneg (extremeSlope μ b false), abs_nonneg (extremeSlope μ b true),
    abs_nonneg (coordinateAllowance shape rate)]

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ShortCrossingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology

theorem sourceEndpoint_transverse (b : ℝ) (n : ℤ) :
    |transverse b (sourceEndpoint b n)| ≤ 1 := by
  have hl := Int.floor_le (b*n)
  have hu := Int.lt_floor_add_one (b*n)
  simp only [sourceEndpoint,transverse]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem sourceEndpoint_distance (b : ℝ) (n : ℤ) (hb : |b| ≤ 1) (hn : 1 ≤ n) :
    ‖latticeEmbed (sourceEndpoint b n)‖ ≤ 3*(n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr := sourceEndpoint_transverse b n
  have ht := abs_add_le (transverse b (sourceEndpoint b n)) (b*(n : ℝ))
  have he : transverse b (sourceEndpoint b n)+b*(n : ℝ)=(⌊b*n⌋ : ℝ) := by
    simp [transverse,sourceEndpoint]
  rw [he,abs_mul,abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at ht
  have hm := mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ n)
  have hh := plane_norm_le_coordinates (latticeEmbed (sourceEndpoint b n))
  change ‖latticeEmbed (sourceEndpoint b n)‖ ≤ |(n : ℝ)|+|(⌊b*n⌋ : ℝ)| at hh
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hh
  linarith

theorem sourceEndpoint_norm_cost (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (n : ℤ) (hn : 0 ≤ n) :
    μ (latticeEmbed (sourceEndpoint b n)) ≤ μ (direction b)*(n : ℝ)+μ transverseUnit := by
  let r := transverse b (sourceEndpoint b n)
  have he : latticeEmbed (sourceEndpoint b n)=(n : ℝ) • direction b+r • transverseUnit := by
    ext i
    fin_cases i <;> simp [r,sourceEndpoint,transverse,latticeEmbed,direction,transverseUnit,
      PiLp.add_apply,PiLp.smul_apply]
    ring
  rw [he]
  have hh := hμ.triangle ((n : ℝ) • direction b) (r • transverseUnit)
  rw [hμ.homogeneous,hμ.homogeneous,abs_of_nonneg (by exact_mod_cast hn : (0 : ℝ) ≤ n)] at hh
  have hr := mul_le_mul_of_nonneg_right (sourceEndpoint_transverse b n) (hμ.nonneg transverseUnit)
  dsimp [r] at hh
  linarith

theorem sourceEndpoint_tube_containment (b C δ s : ℝ) (n : ℤ)
    (hb : |b| ≤ 1) (hs : 1 ≤ s) (hn : 1 ≤ n) (hns : (n : ℝ) ≤ C*s)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4) (hδC : δ*C ≤ 1/2) :
    SegmentTube 0 (sourceEndpoint b n) (δ*n) ⊆ rareFastRegion b 1 8 s n 0 := by
  rintro z ⟨t,ht0,ht1,hd⟩
  let u := latticeEmbed z-segmentPoint 0 (sourceEndpoint b n) t
  have hnorm : ‖u‖ ≤ δ*n := hd
  have hx : u 0=(z.1 : ℝ)-t*n := by
    simp [u,segmentPoint,sourceEndpoint,latticeEmbed,PiLp.sub_apply,PiLp.smul_apply]
  have hr : rCoord b u=transverse b z-t*transverse b (sourceEndpoint b n) := by
    simp [u,segmentPoint,sourceEndpoint,latticeEmbed,transverse,rCoord_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hxbound := (plane_coordinate_le_norm u 0).trans hnorm
  rw [hx] at hxbound
  have hx' := abs_le.mp hxbound
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδn : δ*(n : ℝ) ≤ n/4 := by nlinarith
  have htn : t*(n : ℝ) ≤ n := by nlinarith
  have htn0 : 0 ≤ t*(n : ℝ) := by positivity
  have hrbound := transverse_plane_lipschitz b hb u
  rw [hr] at hrbound
  have hseg : |t*transverse b (sourceEndpoint b n)| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg ht0]
    nlinarith [sourceEndpoint_transverse b n]
  have hsum := abs_add_le (transverse b z-t*transverse b (sourceEndpoint b n))
    (t*transverse b (sourceEndpoint b n))
  rw [sub_add_cancel] at hsum
  have hscale := mul_le_mul_of_nonneg_left hns hδ
  have hscale' := mul_le_mul_of_nonneg_right hδC (by linarith : 0 ≤ s)
  refine ⟨?_,?_,?_⟩
  · simp only [sub_zero,neg_one_mul]
    linarith
  · norm_num only [sub_zero,one_add_one_eq_two]
    linarith
  · simp only [sub_zero]
    nlinarith

/-- For bounded n, a horizontal path suffices; its endpoints need not follow
u because E(s,n) leaves the two endpoint columns unrestricted. -/
theorem horizontal_in_crossingRegion (b s : ℝ) (n : ℤ) (hb : |b| ≤ 1)
    (hn : 0 ≤ n) (hns : (n : ℝ) ≤ 8*s) :
    PathIn 0 (horizontal n) (rareFastRegion b 1 8 s n 0) := by
  intro i _
  have he : displacement ((horizontal n).take i)=(((min i n.toNat : ℕ) : ℤ),0) := by
    simp [horizontal,hn,displacement,Step.delta]
  have hm : (min i n.toNat : ℤ) ≤ n := by
    have := min_le_right i n.toNat
    exact_mod_cast (show (min i n.toNat : ℤ) ≤ n by omega)
  have hm0 : (0 : ℤ) ≤ min i n.toNat := by positivity
  have hm' : ((min i n.toNat : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
  have hm0' : (0 : ℝ) ≤ min i n.toNat := by positivity
  rw [he]
  simp only [zero_add,rareFastRegion,mem_ofPred_eq,sub_zero,transverse,Int.cast_natCast,
    Int.cast_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hm0',neg_one_mul,one_add_one_eq_two]
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hb hm0'
  exact ⟨by linarith,by linarith,by linarith⟩

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ShortCrossingProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Origin-to-endpoint local travel from the actual simultaneous ball event. -/
theorem gamma_origin_local_travel (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (D η δ : ℝ)
    (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ κ > 0, ∀ᶠ s : ℝ in atTop, ∀ q : Vertex, ‖latticeEmbed q‖ ≤ D*s →
      P.real {ω | ¬LocalTravel (gammaMeanNorm h hshape hrate) η δ s 0 q (fun e => τ e ω)} < κ := by
  let _ := h.probability
  intro κ hκ
  filter_upwards [gamma_ball_travel h hshape hrate D η δ hD hη hδ κ hκ,
    eventually_ge_atTop (0 : ℝ)] with s hb hs
  intro q hq
  have hb0 := hb 0
  simp only [shiftEdge, zero_add, Prod.eta] at hb0
  refine (measureReal_mono (μ := P) (show
    {ω | ¬LocalTravel (gammaMeanNorm h hshape hrate) η δ s 0 q (fun e => τ e ω)} ⊆
    {ω | ¬BallTravel (gammaMeanNorm h hshape hrate) D η δ s (fun e => τ e ω)} from ?_)).trans_lt hb0
  intro ω hω hball
  apply hω
  apply hball 0 q ?_ hq
  simpa only [latticeEmbed_zero, norm_zero] using mul_nonneg hD.le hs

/-- Bounded longitudinal scales use an explicit horizontal path. -/
theorem gamma_bounded_crossing_failure (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (b m K s N : ℝ) (n : ℤ) (hb : |b| ≤ 1) (hm : 0 ≤ m)
    (hn : 0 ≤ n) (hnN : (n : ℝ) ≤ N) (hns : (n : ℝ) ≤ 8*s) :
    P.real {ω | (fun e => τ e ω) ∉ crossingEvent b m K s n 0} ≤
      Real.exp (-(rate/2)*(K*s-coordinateAllowance shape rate*N)) := by
  let _ := h.probability
  have hallow := coordinateAllowance_pos hshape hrate
  have hsub : {ω | (fun e => τ e ω) ∉ crossingEvent b m K s n 0} ⊆
      {ω | coordinateAllowance shape rate*(n.natAbs : ℝ)+(K*s-coordinateAllowance shape rate*N) ≤ pathCost (fun e => τ e ω) 0 (horizontal n)} := by
    intro ω hbad
    have hc : m*n+K*s ≤ pathCost (fun e => τ e ω) 0 (horizontal n) := by
      by_contra hh
      apply hbad
      refine ⟨0,horizontal n,⟨rfl,?_⟩,?_,lt_of_not_ge hh⟩
      · simp [displacement_horizontal]
      · intro i hi
        exact (mem_rareFastVertices ..).mpr (horizontal_in_crossingRegion b s n hb hn hns i hi)
    have ha : (n.natAbs : ℝ)=(n : ℝ) := by
      have hi : (n.natAbs : ℤ)=n := by omega
      exact (by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hi)
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    change coordinateAllowance shape rate*(n.natAbs : ℝ)+(K*s-coordinateAllowance shape rate*N) ≤ pathCost (fun e => τ e ω) 0 (horizontal n)
    rw [ha]
    nlinarith
  exact (measureReal_mono hsub).trans (h.costly_horizontal_excess_probability_real hshape hrate 0 n (K*s-coordinateAllowance shape rate*N))

/-- This is the joint short-crossing limit in gr:characteristic-lengths,
expressed as uniform convergence of the failure probabilities. -/
theorem gamma_short_crossing_failure (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b K C : ℝ) (hb : |b| ≤ 1) (hK : 0 < K) (hC : 0 < C) :
    ∀ κ > 0, ∀ᶠ s : ℝ in atTop, ∀ n : ℤ, 1 ≤ n → (n : ℝ) ≤ C*s →
      P.real {ω | (fun e => τ e ω) ∉ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0} < κ := by
  let _ := h.probability
  let η := K/(4*C)
  let δ := min (1/4) (1/(2*C))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hδC : δ*C ≤ 1/2 := by
    have hh := min_le_right (1/4 : ℝ) (1/(2*C))
    have he : δ ≤ (1/2)/C := by
      have heq : (1 : ℝ)/(2*C)=(1/2)/C := by ring
      rw [← heq]
      exact hh
    exact (le_div_iff₀ hC).mp he
  intro κ hκ
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (gamma_origin_local_travel h hshape hrate 3 η δ (by norm_num) hη hδ κ hκ)
  have htail : ∀ᶠ s : ℝ in atTop, Real.exp (-(rate/2)*(K*s-coordinateAllowance shape rate*N)) < κ := by
    filter_upwards [eventually_ge_atTop ((coordinateAllowance shape rate*N+2*(1-Real.log κ)/rate)/K)] with s hs
    have hh := (div_le_iff₀ hK).mp hs
    rw [← Real.exp_log hκ]
    apply Real.exp_lt_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hh hrate.le
    have hid : rate*(2*(1-Real.log κ)/rate)=2*(1-Real.log κ) := by
      field_simp [hrate.ne']
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_ge_atTop N,
    eventually_ge_atTop ((4*(gammaMeanNorm h hshape hrate) transverseUnit+1)/K),htail] with s hs hsN hsNorm htail
  intro n hn hns
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hnN : N ≤ (n : ℝ)
  · have hlt := hN n hnN (sourceEndpoint b n) (by
      simpa only [sub_zero] using sourceEndpoint_distance b n hb hn)
    have hsub : {ω | (fun e => τ e ω) ∉ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0} ⊆
        {ω | ¬LocalTravel (gammaMeanNorm h hshape hrate) η δ n 0 (sourceEndpoint b n) (fun e => τ e ω)} := by
      intro ω hbad hgood
      obtain ⟨ds,hd,hcost,hin⟩ := hgood
      apply hbad
      refine ⟨0,ds,⟨rfl,?_⟩,?_,?_⟩
      · simpa [sourceEndpoint] using congrArg Prod.fst hd
      · intro i hi
        exact (mem_rareFastVertices ..).mpr
          (sourceEndpoint_tube_containment b C δ s n hb hs hn hns hδ.le hδ1 hδC (hin i hi))
      · have hNormBound := sourceEndpoint_norm_cost (gammaMeanNorm h hshape hrate) (gammaMeanNorm_laws h hshape hrate) b n (by omega)
        have hηn : η*(n : ℝ) ≤ K*s/4 := by
          dsimp [η]
          calc
            _ ≤ K/(4*C)*(C*s) := mul_le_mul_of_nonneg_left hns hη.le
            _ = _ := by field_simp
        have hh := (div_le_iff₀ hK).mp hsNorm
        simp only [sub_zero] at hcost
        change pathCost (fun e => τ e ω) 0 ds < (gammaMeanNorm h hshape hrate) (direction b)*n+K*s
        linarith [(gammaMeanNorm_laws h hshape hrate).nonneg transverseUnit]
    exact (measureReal_mono hsub).trans_lt hlt
  · exact (gamma_bounded_crossing_failure h hshape hrate b ((gammaMeanNorm h hshape hrate) (direction b)) K s N n hb ((gammaMeanNorm_laws h hshape hrate).nonneg _)
      (by omega) (le_of_not_ge hnN) (by linarith)).trans_lt htail

/-- Equivalent success-probability formulation from eq:gr-short-crossings. -/
theorem gamma_short_crossing_probability (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b K C : ℝ) (hb : |b| ≤ 1) (hK : 0 < K) (hC : 0 < C) :
    ∀ q < 1, ∀ᶠ s : ℝ in atTop, ∀ n : ℤ, 1 ≤ n → (n : ℝ) ≤ C*s →
      q < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0} := by
  let _ := h.probability
  intro q hq
  filter_upwards [gamma_short_crossing_failure h hshape hrate b K C hb hK hC (1-q) (by linarith)] with s hs
  intro n hn hns
  have hh := hs n hn hns
  have hc := measureReal_compl (μ := P) ((measurableSet_crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0).preimage
    (Measurable.of_eval h.measurable))
  change P.real {ω | (fun e => τ e ω) ∉ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K s n 0} = _ at hc
  rw [hc] at hh
  simpa [Set.preimage] using hh

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CharacteristicLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

theorem firstDyadicExponent_le (p : ℕ → ℝ) (q : ℝ) (j : ℕ) (hj : p j ≤ q) :
    firstDyadicExponent p q ≤ j := by
  have h : ∃ j, p j ≤ q := ⟨j,hj⟩
  simpa only [firstDyadicExponent,dite_eq_left h] using Nat.find_min' h hj

theorem firstDyadicExponent_min (p : ℕ → ℝ) (q : ℝ) (j : ℕ)
    (hj : j < firstDyadicExponent p q) : q < p j := by
  by_contra hh
  exact (not_le_of_gt hj) (firstDyadicExponent_le p q j (le_of_not_gt hh))

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

variable {P τ}

theorem characteristicLength_pos (shape rate : ℝ) (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) :
    0 < characteristicLength P τ shape rate μ b q k := by unfold characteristicLength; positivity

/-- Every smaller dyadic size has crossing probability strictly above q. -/
theorem characteristicLength_minimal (shape rate : ℝ) (μ : Plane → ℝ) (b q : ℝ) (k j : ℕ)
    (hj : (2 : ℤ)^j < characteristicLength P τ shape rate μ b q k) :
    q < sourceDyadicCrossingProbability P τ shape rate μ b k j := by
  have hj' : j < characteristicExponent P τ shape rate μ b q k := by
    by_contra hh
    have he := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (le_of_not_gt hh)
    exact (not_le_of_gt hj) he
  exact firstDyadicExponent_min _ _ _ hj'

/-- The characteristic lengths grow faster than the transverse scale:
`L_k / 2^k → ∞`. -/
theorem gamma_characteristic_lengths_ratio (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun k : ℕ => (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ)/(2 : ℝ)^k) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let C := max 1 B
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hK : 0 < sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b := by unfold sourceCrossingK; positivity
  have hs := gamma_short_crossing_probability h hshape hrate b (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b) C hb hK hC q hq1
  have h2 := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2)
  filter_upwards [h2.eventually hs,gamma_characteristic_lengths_exist h hshape hrate b q hb hq] with k hk he
  have hL : 1 ≤ characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k := characteristicLength_pos shape rate (gammaMeanNorm h hshape hrate) b q k
  have hgt : C*(2 : ℝ)^k < (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ) := by
    by_contra hn
    exact (not_lt_of_ge he.2) (hk _ hL (le_of_not_gt hn))
  have hr : C < (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ)/(2 : ℝ)^k :=
    (lt_div_iff₀ (by positivity)).mpr hgt
  exact (le_max_right _ _).trans hr.le

/-- Characteristic lengths have arbitrarily large record scales satisfying
the dyadic comparison bound. -/
theorem gamma_characteristic_record_scales (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
    ∃ k0 : ℕ, ∀ N, ∃ k, N < k ∧ k0 ≤ k ∧
      ∀ j, j ≤ k-k0 → (1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ) ≤
        (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q (k-j) : ℝ) := by
  obtain ⟨k0,hk0⟩ := eventually_atTop.mp (gamma_characteristic_lengths_exist h hshape hrate b q hb hq)
  refine ⟨k0,record_scales_from (fun k => (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k : ℝ)) k0 (fun k _ => by exact_mod_cast characteristicLength_pos shape rate (gammaMeanNorm h hshape hrate) b q k) ?_⟩
  intro k hk
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (hk0 k hk).1
  have he : characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k ≤ (2 : ℤ)^(3*k) := hh
  exact_mod_cast he

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridMeshes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer meshes with a final unit interval, and their comparison with
characteristic lengths at record indices. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Filter Set MeasureTheory
open scoped Topology

lemma gridMesh_pos (m j : ℕ) : 0 < gridMesh m j := by unfold gridMesh; positivity
lemma gridWidth_pos (k j : ℕ) : 0 < gridWidth k j := by unfold gridWidth; positivity

lemma gridMesh_level_bound (m k j : ℕ) (hm : m ≤ 3*k) (hj : j ≤ gridLastLevel m) :
    4*(k-j)+3 ≥ k := by
  unfold gridLastLevel at hj
  omega

lemma gridMesh_count_ratio (m j : ℕ) :
    (2 : ℝ)^m / (gridMesh m j : ℝ) ≤ (2 : ℝ)^(4*j+1) := by
  have hg : (0 : ℝ) < (gridMesh m j : ℝ) := by exact_mod_cast gridMesh_pos m j
  rw [div_le_iff₀ hg]
  simp only [gridMesh,Int.cast_pow,Int.cast_ofNat,← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  unfold gridMeshExponent
  omega

lemma gridWidth_ratio (k j : ℕ) (hj : j ≤ k) :
    (2 : ℝ)^k / (gridWidth k j : ℝ) = (2 : ℝ)^j := by
  have he : k=j+(k-j) := by omega
  simp only [gridWidth,Int.cast_pow,Int.cast_ofNat]
  rw [show (2 : ℝ)^k=(2 : ℝ)^j*(2 : ℝ)^(k-j) by rw [← pow_add,← he]]
  rw [mul_div_cancel_right₀ _ (by positivity)]

lemma gridMesh_below_record_length (L : ℕ → ℤ) (k m j : ℕ)
    (hL : L k=(2 : ℤ)^m)
    (hrec : (1/16 : ℝ)^j*(L k : ℝ) ≤ (L (k-j) : ℝ))
    (hunit : 1 < L (k-j)) : gridMesh m j < L (k-j) := by
  by_cases hsmall : m ≤ 4*j+1
  · simpa [gridMesh,gridMeshExponent,Nat.sub_eq_zero_of_le hsmall] using hunit
  · have he : m=gridMeshExponent m j+(4*j+1) := by unfold gridMeshExponent; omega
    have hr : (1/16 : ℝ)^j*((2 : ℤ)^m : ℝ) = 2*(gridMesh m j : ℝ) := by
      simp only [Int.cast_pow,Int.cast_ofNat,gridMesh]
      conv_lhs => rw [he,pow_add]
      rw [pow_add,pow_one,show (2 : ℝ)^(4*j)=(16 : ℝ)^j by rw [pow_mul]; norm_num]
      have hh : (1/16 : ℝ)^j*16^j=1 := by rw [← mul_pow]; norm_num
      calc
        _ = (2 : ℝ)^gridMeshExponent m j*((1/16 : ℝ)^j*16^j)*2 := by ring
        _ = _ := by rw [hh]; ring
    rw [hL] at hrec
    simp only [Int.cast_pow,Int.cast_ofNat] at hrec hr
    rw [hr] at hrec
    have hp : (0 : ℝ) < gridMesh m j := by exact_mod_cast gridMesh_pos m j
    exact_mod_cast (show (gridMesh m j : ℝ) < L (k-j) by linarith)

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Crossing trial probabilities at every allowed level of each sufficiently
large characteristic record index. -/
theorem gamma_grid_trial_probabilities (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ,
      j ≤ gridLastLevel (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) →
      ((1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k : ℝ) ≤
        (characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) : ℝ)) →
      q₀ < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b ((gammaMeanNorm henv hs hr) (direction b))
        (sourceCrossingK shape rate (gammaMeanNorm henv hs hr) b) (gridWidth k j) (gridMesh (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) j) 0} := by
  have hlarge := (gamma_characteristic_lengths_ratio henv hs hr b q₀ hb hq hq1).eventually
    (eventually_gt_atTop (1 : ℝ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlarge
  filter_upwards [eventually_ge_atTop (4*N+4),
    gamma_characteristic_lengths_exist henv hs hr b q₀ hb hq] with k hk hex
  intro j hj hrec
  have hlev := gridMesh_level_bound (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) k j hex.1 hj
  have hjk : j ≤ k := by unfold gridLastLevel at hj; omega
  have hNk : N ≤ k-j := by omega
  have hunit : 1 < characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2^(k-j))).mp (hN (k-j) hNk)
    have hp : (1 : ℝ) ≤ 2^(k-j) := one_le_pow₀ (by norm_num)
    exact_mod_cast (show (1 : ℝ) < characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) by linarith)
  have hmesh := gridMesh_below_record_length (characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀) k
    (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) j rfl hrec hunit
  have hp := characteristicLength_minimal shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j)
    (gridMeshExponent (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) j) hmesh
  simpa only [sourceDyadicCrossingProbability,gridWidth,gridMesh,Int.cast_pow,Int.cast_ofNat] using hp

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite supersets of grid intervals and transverse bins, with cardinality
bounds independent of the characteristic scale. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Finset Set

lemma gridIndexRange_card (x : ℝ) : (gridIndexRange x).card=2*⌈x⌉₊+1 := by
  rw [gridIndexRange,Int.card_Icc]
  omega

lemma gridIndexConstant_pos (A R : ℝ) (hA : 0 < A) (hR : 0 < R) :
    0 < gridIndexConstant A R := by unfold gridIndexConstant; positivity

lemma gridTestIndices_card (A R L s l w : ℝ) (hA : 0 < A) (hR : 0 < R)
    (hl : 0 < l) (hw : 0 < w) (hLl : 1 ≤ L/l) (hsw : 1 ≤ s/w) :
    ((gridTestIndices A R L s l w).card : ℝ) ≤
      (2*(A+4)+3)*(2*R+5)*(L/l)*(s/w) := by
  have hL : 0 ≤ L := by have hh := (le_div_iff₀ hl).mp hLl; linarith
  have hs : 0 ≤ s := by have hh := (le_div_iff₀ hw).mp hsw; linarith
  have hc₁ := Nat.ceil_lt_add_one (show 0 ≤ (A+4)*L/l by positivity)
  have hc₂ := Nat.ceil_lt_add_one (show 0 ≤ R*s/w+1 by positivity)
  have hc₁' : 2*(⌈(A+4)*L/l⌉₊ : ℝ)+1 ≤ (2*(A+4)+3)*(L/l) := by
    simp only [mul_div_assoc] at hc₁ ⊢
    nlinarith
  have hc₂' : 2*(⌈R*s/w+1⌉₊ : ℝ)+1 ≤ (2*R+5)*(s/w) := by
    simp only [mul_div_assoc] at hc₂ ⊢
    nlinarith
  rw [gridTestIndices,Finset.card_product,gridIndexRange_card,gridIndexRange_card]
  push_cast
  have hh := mul_le_mul hc₁' hc₂' (by positivity) (by positivity)
  nlinarith

lemma gridTestIndices_level_card (A R : ℝ) (hA : 0 < A) (hR : 0 < R)
    (k m j : ℕ) (hj : j ≤ k) :
    ((gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k)
      (gridMesh m j) (gridWidth k j)).card : ℝ) ≤ gridIndexConstant A R*(2 : ℝ)^(5*j) := by
  have hl : (0 : ℝ) < gridMesh m j := by exact_mod_cast gridMesh_pos m j
  have hw : (0 : ℝ) < gridWidth k j := by exact_mod_cast gridWidth_pos k j
  have hLl : 1 ≤ (2 : ℝ)^m/(gridMesh m j : ℝ) := by
    apply (le_div_iff₀ hl).mpr
    simp only [one_mul,gridMesh,Int.cast_pow,Int.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hsw : 1 ≤ (2 : ℝ)^k/(gridWidth k j : ℝ) := by
    rw [gridWidth_ratio k j hj]
    exact one_le_pow₀ (by norm_num)
  apply (gridTestIndices_card A R _ _ _ _ hA hR hl hw hLl hsw).trans
  rw [gridWidth_ratio k j hj]
  calc
    _ ≤ (2*(A+4)+3)*(2*R+5)*(2 : ℝ)^(4*j+1)*(2 : ℝ)^j := by
      gcongr
      exact gridMesh_count_ratio m j
    _ = _ := by
      rw [mul_assoc ((2*(A+4)+3)*(2*R+5)),← pow_add,
        show 4*j+1+j=5*j+1 by omega,pow_succ]
      unfold gridIndexConstant
      ring

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set Finset MeasureTheory ProbabilityTheory

lemma mem_arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) (w : Edge → ℝ) :
    w ∈ arbitraryEndpointEvent b m₀ a A R ε k m ↔
      ∃ p ds, PathIn p ds (endpointBox b A R k m) ∧ defect w b m₀ a p ds < -ε*(2 : ℝ)^k := by
  have hv : (endpointBoxVertices b A R k m : Set Vertex)=endpointBox b A R k m :=
    (endpointBox_finite b A R k m).coe_toFinset
  simp only [arbitraryEndpointEvent,strictLocalizedEvent,mem_ofPred_eq,true_and,hv,defect]
  constructor <;> rintro ⟨p,ds,hin,hc⟩ <;> exact ⟨p,ds,hin,by linarith⟩

lemma measurableSet_arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) :
    MeasurableSet (arbitraryEndpointEvent b m₀ a A R ε k m) :=
  measurableSet_strictLocalizedEvent _ _ _

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Grid
open Filter Finset Set
open scoped Topology

lemma summable_grid_gaussian (a : ℝ) (ha : 0 < a) :
    Summable (fun j : ℕ => (2 : ℝ)^(5*j)*Real.exp (-a*(j : ℝ)^2)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((5*Real.log 2+1)/a)
  apply (summable_nat_add_iff N).mp
  have hs : Summable (fun n : ℕ => Real.exp (-1)^n) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by norm_num))
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro n
  have hNa : 5*Real.log 2+1 < (N : ℝ)*a := (div_lt_iff₀ ha).mp hN
  have hja : 5*Real.log 2+1 ≤ a*((n+N : ℕ) : ℝ) := by push_cast; nlinarith
  have hmul := mul_le_mul_of_nonneg_right hja (show 0 ≤ ((n+N : ℕ) : ℝ) by positivity)
  rw [show (2 : ℝ)^(5*(n+N))=Real.exp ((5*(n+N : ℕ) : ℕ)*Real.log 2) by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)],← Real.exp_add,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast at hmul ⊢
  nlinarith

lemma gridFailureSeries_nonneg (shape : ℝ) (_hs : 0 < shape) (q : ℝ) (j : ℕ) : 0 ≤ gridFailureSeries shape q j := by
  unfold gridFailureSeries
  positivity

lemma summable_gridFailureSeries (shape : ℝ) (hs : 0 < shape) (q : ℝ) (hq : 0 < q) : Summable (gridFailureSeries shape q) := by
  have h := (summable_grid_gaussian q hq).add
    ((summable_grid_gaussian (verticalExponent shape) (verticalExponent_pos hs)).mul_left 2)
  apply h.congr
  intro j
  unfold gridFailureSeries
  ring

lemma grid_level_failure_le_series (shape : ℝ) (hs : 0 < shape) (q : ℝ) (_hq : 0 ≤ q) (hq1 : q ≤ 1)
    (j : ℕ) (w : ℝ) (hw : 1 ≤ w) :
    (2 : ℝ)^(5*j)*((1-q)^(j^2)+2*Real.exp (-(verticalExponent shape)*(j : ℝ)^2*w)) ≤
      gridFailureSeries shape q j := by
  have hb : 1-q ≤ Real.exp (-q) := by have hh := Real.add_one_le_exp (-q); linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ 1-q by linarith) hb (j^2)
  have hp' : (1-q)^(j^2) ≤ Real.exp (-q*(j : ℝ)^2) := by
    rw [← Real.exp_nat_mul] at hp
    simpa only [Nat.cast_pow,mul_comm] using hp
  have he : Real.exp (-(verticalExponent shape)*(j : ℝ)^2*w) ≤
      Real.exp (-(verticalExponent shape)*(j : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left hw
      (mul_nonneg (verticalExponent_pos hs).le (sq_nonneg (j : ℝ)))
    nlinarith
  unfold gridFailureSeries
  gcongr

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RecordGridProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Simultaneous finite-grid probability bound from subcharacteristic
crossing bounds. -/
theorem gridConnectionsEvent_failure_bound (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (b m₀ K A R q₀ : ℝ) (hA : 0 < A) (hR : 0 < R) (hq : 0 < q₀) (hq1 : q₀ ≤ 1)
    (k m J : ℕ) (hJ : 1 ≤ J) (hlast : gridLastLevel m ≤ k)
    (htrial : ∀ j, J ≤ j → j ≤ gridLastLevel m →
      q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m₀ K (gridWidth k j) (gridMesh m j) 0}) :
    P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b m₀ K A R k m J} ≤
      Grid.gridFailureTail shape (gridIndexConstant A R) q₀ J := by
  let _ := henv.probability
  let N := gridLastLevel m+1-J
  let S (n : ℕ) := gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k) (gridMesh m (n+J)) (gridWidth k (n+J))
  let Bad (n : ℕ) (ih : ℤ×ℤ) : Set Ω := {ω | (fun e => τ e ω) ∉ gridBinGood shape rate b m₀ K
    (gridMesh m (n+J)*ih.1) ih.2 (gridWidth k (n+J)) (gridMesh m (n+J)) (n+J)}
  let AllBad : Set Ω := ⋃ n ∈ Finset.range N, ⋃ ih ∈ S n, Bad n ih
  have hsub : ∀ᵐ ω ∂P, (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b m₀ K A R k m J → ω ∈ AllBad := by
    filter_upwards [henv.ae_positive] with ω hω hb
    have ht : ¬(fun e => τ e ω) ∈ gridTestsEvent shape rate b m₀ K A R k m J := by
      intro ht
      exact hb ⟨fun e => (hω e).le,ht⟩
    simp only [gridTestsEvent,Set.mem_ofPred_eq,not_forall] at ht
    obtain ⟨n,hn,ih,hih,hbad⟩ := ht
    exact mem_iUnion₂.mpr ⟨n,hn,mem_iUnion₂.mpr ⟨ih,hih,hbad⟩⟩
  have hprob : P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b m₀ K A R k m J} ≤ P.real AllBad :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have hC : 0 ≤ gridIndexConstant A R := (gridIndexConstant_pos A R hA hR).le
  have hlevel (n : ℕ) (hn : n ∈ Finset.range N) :
      P.real (⋃ ih ∈ S n, Bad n ih) ≤ gridIndexConstant A R*Grid.gridFailureSeries shape q₀ (n+J) := by
    have hn' : n+J ≤ gridLastLevel m := by have hh := Finset.mem_range.mp hn; dsimp [N] at hh; omega
    have hjk : n+J ≤ k := hn'.trans hlast
    let d := (1-q₀)^((n+J)^2)+2*Real.exp (-(Grid.verticalExponent shape)*((n+J : ℕ) : ℝ)^2*(gridWidth k (n+J)))
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hb (ih : ℤ×ℤ) : P.real (Bad n ih) ≤ d :=
      gridBinGood_failure_bound henv hs hr b m₀ K q₀ _ _ _ _ (n+J) (by omega)
        (gridWidth_pos k (n+J)) (htrial (n+J) (by omega) hn')
    calc
      _ ≤ ∑ ih ∈ S n,P.real (Bad n ih) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ih ∈ S n,d := Finset.sum_le_sum (fun ih _ => hb ih)
      _ = ((S n).card : ℝ)*d := by simp
      _ ≤ (gridIndexConstant A R*(2 : ℝ)^(5*(n+J)))*d :=
        mul_le_mul_of_nonneg_right (gridTestIndices_level_card A R hA hR k m (n+J) hjk) hd
      _ ≤ gridIndexConstant A R*Grid.gridFailureSeries shape q₀ (n+J) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hC
        exact Grid.grid_level_failure_le_series shape hs q₀ hq.le hq1 (n+J)
          (gridWidth k (n+J)) (by exact_mod_cast gridWidth_pos k (n+J))
  calc
    _ ≤ P.real AllBad := hprob
    _ ≤ ∑ n ∈ Finset.range N,P.real (⋃ ih ∈ S n, Bad n ih) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.range N,gridIndexConstant A R*Grid.gridFailureSeries shape q₀ (n+J) :=
      Finset.sum_le_sum hlevel
    _ = gridIndexConstant A R*(∑ n ∈ Finset.range N,Grid.gridFailureSeries shape q₀ (n+J)) := by rw [Finset.mul_sum]
    _ ≤ gridIndexConstant A R*(∑' n : ℕ,Grid.gridFailureSeries shape q₀ (n+J)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact (Grid.summable_gridFailureSeries shape hs q₀ hq).comp_injective (fun _ _ h => Nat.add_right_cancel h)
        |>.sum_le_tsum (Finset.range N) (fun _ _ => Grid.gridFailureSeries_nonneg shape hs q₀ _)
    _ = _ := rfl

/-- Arbitrarily large characteristic record scales carry simultaneous grid
bounds, independently of the box parameters and initial level. -/
theorem gamma_simultaneous_grid_scales (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∀ N : ℕ, ∃ k : ℕ, N < k ∧ k₀ ≤ k ∧
      (∀ j, j ≤ k-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k : ℝ) ≤
        (characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) : ℝ)) ∧
      ∀ A R : ℝ, 0 < A → 0 < R → ∀ J : ℕ, 1 ≤ J →
        P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b ((gammaMeanNorm henv hs hr) (direction b))
          (sourceCrossingK shape rate (gammaMeanNorm henv hs hr) b) A R k (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) J} ≤
          Grid.gridFailureTail shape (gridIndexConstant A R) q₀ J := by
  obtain ⟨k₀,hrec⟩ := gamma_characteristic_record_scales henv hs hr b q₀ hb hq
  have he := (gamma_characteristic_lengths_exist henv hs hr b q₀ hb hq).and
    (gamma_grid_trial_probabilities henv hs hr b q₀ hb hq hq1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  refine ⟨k₀,?_⟩
  intro N
  obtain ⟨k,hk,hkk₀,hkr⟩ := hrec (max N (max N₀ (4*k₀+4)))
  have hkN : N < k := (le_max_left _ _).trans_lt hk
  have hkN₀ : N₀ ≤ k := by omega
  have hklarge : 4*k₀+4 ≤ k := by omega
  obtain ⟨hex,hp⟩ := hN₀ k hkN₀
  have hlast : gridLastLevel (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) ≤ k-k₀ := by
    unfold gridLastLevel
    omega
  refine ⟨k,hkN,hkk₀,hkr,?_⟩
  intro A R hA hR J hJ
  apply gridConnectionsEvent_failure_bound henv hs hr b ((gammaMeanNorm henv hs hr) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm henv hs hr) b)
    A R q₀ hA hR hq hq1.le k (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) J hJ
    (hlast.trans (Nat.sub_le _ _))
  intro j _ hj
  exact (hp j hj (hkr j (hj.trans hlast))).le

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Lemma `gr:variable-endpoints` on characteristic record scales, chosen
independently of the box parameters, deficit, and sign. -/
theorem gamma_arbitraryEndpoint_record_scales (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ plus : Bool,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b ((gammaMeanNorm henv hshape hrate) (direction b))
          (extremeSlope (gammaMeanNorm henv hshape hrate) b plus) A R ε (k n) (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n))}) atTop (𝓝 0) := by
  obtain ⟨k₀,hscales⟩ := gamma_simultaneous_grid_scales henv hshape hrate b q₀ hb hq hq1
  choose k hk hk₀ hrec hgrid using hscales
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hk n).le
  refine ⟨k₀,k,hkt,fun n => ⟨hk n,hk₀ n,hrec n⟩,?_⟩
  intro A R ε hA hR hε plus
  have hratio : Tendsto (fun n => (2 : ℝ)^(characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n))/(2 : ℝ)^(k n)) atTop atTop := by
    convert (gamma_characteristic_lengths_ratio henv hshape hrate b q₀ hb hq hq1).comp hkt using 1
    ext n
    simp [characteristicLength]
  have hm : ∀ᶠ n : ℕ in atTop, characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n) ≤ 3*k n := by
    filter_upwards [hkt.eventually (gamma_characteristic_lengths_exist henv hshape hrate b q₀ hb hq)] with n hn
    exact hn.1
  exact gamma_arbitraryEndpoint_tendsto_of_grids henv hshape hrate b (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) A R ε q₀
    hb (sourceCrossingK_ge_hundred shape rate (gammaMeanNorm henv hshape hrate) b) hA hR hε hq plus k
    (fun n => characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n)) hkt hratio hm
    (fun J hJ => Eventually.of_forall (fun n => hgrid n A R hA hR J hJ))

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

/-- Exact source event in a translated box, with unrestricted endpoints. -/
lemma mem_translatedArbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ translatedArbitraryEndpointEvent b m₀ a A R ε k m t ↔
      ∃ p ds, PathIn p ds {z | z-t ∈ endpointBox b A R k m} ∧ defect w b m₀ a p ds < -ε*(2 : ℝ)^k := by
  change (fun e => w (shiftEdge t e)) ∈ arbitraryEndpointEvent b m₀ a A R ε k m ↔ _
  rw [mem_arbitraryEndpointEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m₀ a p ds=defect w b m₀ a (t+p) ds := by
    simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hin,hcost⟩
    refine ⟨t+p,ds,?_,by rwa [← hc]⟩
    intro i hi
    have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
    simpa only [mem_ofPred_eq,he] using hin i hi
  · rintro ⟨p,ds,hin,hcost⟩
    refine ⟨p-t,ds,?_,?_⟩
    · intro i hi
      have he : p-t+displacement (ds.take i)=p+displacement (ds.take i)-t := by abel
      simpa only [mem_ofPred_eq,he] using hin i hi
    · rw [hc,add_sub_cancel]
      exact hcost

lemma mem_eitherEndpointEvent (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ eitherEndpointEvent b m₀ am ap A R ε k m t ↔
      ∃ p ds, PathIn p ds {z | z-t ∈ endpointBox b A R k m} ∧
        (defect w b m₀ am p ds < -ε*(2 : ℝ)^k ∨ defect w b m₀ ap p ds < -ε*(2 : ℝ)^k) := by
  simp only [eitherEndpointEvent,mem_union,mem_translatedArbitraryEndpointEvent]
  constructor
  · rintro (⟨p,ds,hin,hc⟩ | ⟨p,ds,hin,hc⟩)
    · exact ⟨p,ds,hin,Or.inl hc⟩
    · exact ⟨p,ds,hin,Or.inr hc⟩
  · rintro ⟨p,ds,hin,hc | hc⟩
    · exact Or.inl ⟨p,ds,hin,hc⟩
    · exact Or.inr ⟨p,ds,hin,hc⟩

lemma spatialWitness_good_event (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ)
    (p : GammaFPP.BK.StrictPathWitness) (hp : p ∈ spatialWitnessFamily b m₀ am ap K η k m ih)
    (w : Edge → ℝ) (hw : p.Good w) : w ∈ spatialRareEvent b m₀ am ap K η k m ih := by
  rcases hp with ⟨hin,hbound | hbound⟩ | ⟨hstart,hend,hin,hbound⟩
  · apply Or.inl
    apply (mem_eitherEndpointEvent ..).mpr
    refine ⟨p.start,p.steps,hin,Or.inl ?_⟩
    change pathCost w p.start p.steps < p.bound at hw
    unfold defect
    rw [hbound] at hw
    linarith
  · apply Or.inl
    apply (mem_eitherEndpointEvent ..).mpr
    refine ⟨p.start,p.steps,hin,Or.inr ?_⟩
    change pathCost w p.start p.steps < p.bound at hw
    unfold defect
    rw [hbound] at hw
    linarith
  · apply Or.inr
    refine ⟨p.start,p.steps,⟨hstart,hend⟩,?_,?_⟩
    · intro i hi
      exact (mem_rareFastVertices ..).mpr (hin i hi)
    · simpa only [GammaFPP.BK.StrictPathWitness.Good,Int.cast_pow,Int.cast_ofNat,hbound] using hw

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointTranslationProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK Set Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma eitherEndpointEvent_probability_translate (henv : GammaEnvironment shape rate P τ)
    (_hshape : 0 < shape) (_hrate : 0 < rate)
    (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b m₀ am ap A R ε k m t} =
      P {ω | (fun e => τ e ω) ∈
        arbitraryEndpointEvent b m₀ am A R ε k m ∪ arbitraryEndpointEvent b m₀ ap A R ε k m} := by
  exact henv.translated_event_probability t _
    ((measurableSet_arbitraryEndpointEvent ..).union (measurableSet_arbitraryEndpointEvent ..))

/-- Full arbitrary-endpoint lemma, both signs and uniformly translated boxes,
for the deterministic norm supplied by the actual Gamma environment. -/
theorem gamma_arbitrary_endpoints (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ t : ℕ → Vertex,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b
          ((gammaMeanNorm henv hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm henv hshape hrate) b false)
          (extremeSlope (gammaMeanNorm henv hshape hrate) b true) A R ε (k n)
          (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n)) (t n)}) atTop (𝓝 0) := by
  let _ := henv.probability
  obtain ⟨k₀,k,hkt,hrec,hl⟩ := gamma_arbitraryEndpoint_record_scales henv hshape hrate b q₀ hb hq hq1
  refine ⟨k₀,k,hkt,hrec,?_⟩
  intro A R ε hA hR hε t
  have hsum := (hl A R ε hA hR hε false).add (hl A R ε hA hR hε true)
  simp only [add_zero] at hsum
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hsum
  intro n
  unfold Measure.real
  rw [eitherEndpointEvent_probability_translate henv hshape hrate]
  exact measureReal_union_le _ _

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialRareProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK Set Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- A single actual scale works simultaneously for every spatial index, and
can also exceed any requested transverse scale and longitudinal aspect ratio. -/
theorem gamma_spatial_rare_scales (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k : ℝ) ∧
      ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b
        ((gammaMeanNorm henv hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm henv hshape hrate) b false)
        (extremeSlope (gammaMeanNorm henv hshape hrate) b true) (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) η k
        (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k) ih} ≤ 2*q₀ := by
  let _ := henv.probability
  let μ := (gammaMeanNorm henv hshape hrate)
  obtain ⟨k₀,k,hkt,_hrec,hend⟩ := gamma_arbitrary_endpoints henv hshape hrate b q₀ hb hq hq1
  have he := hend 4 4 η (by norm_num) (by norm_num) hη (fun _ => 0)
  have hs := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hkt
  have hr := (gamma_characteristic_lengths_ratio henv hshape hrate b q₀ hb hq hq1).comp hkt
  have hc := hkt.eventually (gamma_characteristic_lengths_exist henv hshape hrate b q₀ hb hq)
  obtain ⟨n,hn,hns,hnr,hnc,hne⟩ := ((hkt.eventually (eventually_gt_atTop N)).and
    ((hs.eventually (eventually_ge_atTop S)).and
    ((hr.eventually (eventually_ge_atTop D)).and (hc.and (he.eventually (gt_mem_nhds hq)))))).exists
  refine ⟨k n,hn,hns,(le_div_iff₀ (by positivity : (0 : ℝ) < 2^(k n))).mp hnr,?_⟩
  intro ih
  let m := characteristicExponent P τ shape rate μ b q₀ (k n)
  let v := spatialTranslate b (k n) m ih
  let v' := spatialTranslate b (k n) m (ih+(1,0))
  have hp : P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
      (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v} ≤ q₀ := by
    have heq : P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
        (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v} =
      P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
        (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m 0} := by
      unfold Measure.real
      rw [eitherEndpointEvent_probability_translate henv hshape hrate,eitherEndpointEvent_probability_translate henv hshape hrate]
    rw [heq]
    exact hne.le
  have hcross : P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
      (sourceCrossingK shape rate μ b) ((2 : ℝ)^(k n)) ((2 : ℤ)^m) v'} ≤ q₀ := by
    unfold Measure.real
    rw [crossingEvent_probability_translate henv]
    exact hnc.2
  have hu := measureReal_union_le (μ := P)
    {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
      (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v}
    {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
      (sourceCrossingK shape rate μ b) ((2 : ℝ)^(k n)) ((2 : ℤ)^m) v'}
  change _ ≤ 2*q₀
  exact hu.trans (by linarith)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialWitnessProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK Set Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Actual spatial path witnesses obey BK for every finite list of indices,
including repeated indices and overlapping boxes. -/
theorem gamma_spatial_witness_BK (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b m₀ am ap K η p₀ : ℝ) (hp₀ : 0 ≤ p₀) (k m : ℕ)
    (hrare : ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b m₀ am ap K η k m ih} ≤ p₀)
    (is : List (ℤ×ℤ)) :
    P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ p₀^is.length := by
  let _ := henv.probability
  let S := spatialListSupport b k m is
  have hsingle (ih : ℤ×ℤ) : P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
      (fun e => τ e ω)} ≤ p₀ := by
    apply (measureReal_mono (μ := P) (s₂ := {ω | (fun e => τ e ω) ∈
      spatialRareEvent b m₀ am ap K η k m ih}) ?_).trans (hrare ih)
    rintro ω ⟨p,hp,_he,hg⟩
    exact spatialWitness_good_event b m₀ am ap K η k m ih p hp _ hg
  apply (GammaFPP.BK.gamma_strict_path_BK henv hshape hrate S (is.map (spatialWitnessFamily b m₀ am ap K η k m))).trans
  simp only [List.map_map]
  have hprod (js : List (ℤ×ℤ)) :
      (js.map (fun ih => P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
        (fun e => τ e ω)})).prod ≤ p₀^js.length := by
    induction js with
    | nil => simp
    | cons i js ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
      calc
        _ ≤ p₀*(js.map (fun ih => P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
          (fun e => τ e ω)})).prod := mul_le_mul_of_nonneg_right (hsingle i) (List.prod_nonneg (by intro a ha; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha; exact measureReal_nonneg))
        _ ≤ p₀*p₀^js.length := mul_le_mul_of_nonneg_left ih hp₀
        _ = _ := by ring
  exact hprod is

/-- The finite-list bound with the rare-event probabilities supplied by the
actual model, at one common scale for every list of spatial indices. -/
theorem gamma_spatial_witness_BK_scales_oai (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k : ℝ) ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths
        (spatialListSupport b k (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k) is)
        (is.map (spatialWitnessFamily b ((gammaMeanNorm henv hshape hrate) (direction b))
          (extremeSlope (gammaMeanNorm henv hshape hrate) b false) (extremeSlope (gammaMeanNorm henv hshape hrate) b true)
          (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) η k
          (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k))) (fun e => τ e ω)} ≤
        (2*q₀)^is.length := by
  obtain ⟨k,hk,hs,hd,hrare⟩ := gamma_spatial_rare_scales henv hshape hrate b q₀ η hb hq hq1 hη N S D
  refine ⟨k,hk,hs,hd,?_⟩
  intro is
  exact gamma_spatial_witness_BK henv hshape hrate b _ _ _ _ η (2*q₀) (by positivity) k
    (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k) hrare is

end GammaFPP.CrossingBridge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales_oai.{u_1} := @OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales_oai.{u_1}
