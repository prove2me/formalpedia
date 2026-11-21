-- Prove2me | solution 1 for MoranYanPAC.Main.private_pac_nearly_linear
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T15:33:48.0785+00:00
-- url     : https://prove2.me/submissions/5000f6ed-6735-45aa-9d1c-d4ac94fdb211
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_PrivLittlestone_rankLayer
import Definitions.Def_PrivLittlestone_restrictCls
import Definitions.Def_PrivLittlestone_rankOf
import Definitions.Def_PrivLittlestone_witnessSpace
import Definitions.Def_PrivLittlestone_IsWitnessAssignment
import Definitions.Def_PrivLittlestone_versionCell
import Definitions.Def_PrivLittlestone_selDesc
import Definitions.Def_PrivLittlestone_selD
import Definitions.Def_PrivLittlestone_selT
import Definitions.Def_MoranYanPAC_Main_GoodFamily
import Definitions.Def_MoranYanPAC_Main_Candidates
import Theorems.Thm_MoranYanPAC_Main_dimension_decreases_with_rank
import Theorems.Thm_PrivLittlestone_eq_21
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MoranYanPAC_Main_PACExperiment
import Definitions.Def_MoranYanPAC_Learner
import Theorems.Thm_MoranYanPAC_Main_structural_exponential_mechanism
import Theorems.Thm_MoranYanPAC_Main_global_local_candidate_counts
import Theorems.Thm_MoranYanPAC_Main_vc_generalization
import Theorems.Thm_MoranYanPAC_Main_small_witnesses_with_soa
import Theorems.Thm_MoranYanPAC_Learner_conditionalSuccess_aemeasurable
section
set_option autoImplicit false

namespace PrivLittlestone.Dev.Sel

variable {X : Type*}

theorem selDesc_prop (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) (k : ℕ) :
    ∀ g ∈ selDesc H d Aw V k, g ∈ V ∧ d - k ≤ rankOf H d g := by
  induction k with
  | zero => intro g hg; exact ⟨hg.1, by simp [hg.2]⟩
  | succ k ih =>
    intro g hg
    simp only [selDesc] at hg
    split_ifs at hg with hk
    · rcases hg with hg | hg
      · have := ih g hg; exact ⟨this.1, by omega⟩
      · exact ⟨hg.1, by rw [hg.2.1]⟩
    · have := ih g hg; exact ⟨this.1, by omega⟩

end PrivLittlestone.Dev.Sel

namespace PrivLittlestone

open PrivLittlestone.Dev.Sel

end PrivLittlestone
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Basic

open UnderstandingML

variable {X : Type*}

end MoranYanPAC.Dev.Basic
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Dim

open UnderstandingML MoranYanPAC.Dev.Basic PrivLittlestone

variable {X : Type*}

end MoranYanPAC.Dev.Dim
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.L11a

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim PrivLittlestone MoranYanPAC.Main

variable {X : Type*}

theorem selD_sub_union (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) :
    selD H d Aw V ⊆ ⋃ s ∈ Finset.range (d + 1), selT H d Aw V s := by
  have : ∀ k, selDesc H d Aw V k ⊆ ⋃ s ∈ Finset.range (d + 1), selT H d Aw V s := by
    intro k
    induction k with
    | zero =>
      intro g hg
      simp only [Set.mem_iUnion]
      exact ⟨d, by simp, hg.1, hg.2, fun _ hlt => absurd hlt (lt_irrefl _)⟩
    | succ k ih =>
      intro g hg
      have hg' := hg
      simp only [selDesc] at hg'
      split_ifs at hg' with hk
      · rcases hg' with hg' | hg'
        · exact ih hg'
        · simp only [Set.mem_iUnion]
          refine ⟨d - (k + 1), by simp only [Finset.mem_range]; omega, hg'.1, hg'.2.1, fun _ _ hmem => ?_⟩
          have : d - (d - (k + 1)) - 1 = k := by omega
          rw [this] at hmem
          exact hg'.2.2 _ hmem
      · exact ih hg'
  exact this d


end MoranYanPAC.Dev.L11a
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartA
open MoranYanPAC.Main MoranYanPAC.Learner PrivLittlestone UnderstandingML
/-- Lemma 6 gives a witness assignment with the SOA clause. -/
theorem exists_sourceWitnesses {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) :
    ∃ Aw : (X → Bool) → Finset X, SourceWitnesses H d Aw := by
  classical
  have L6 := small_witnesses_with_soa H d hH hd hd1
  let Aw : (X → Bool) → Finset X := fun h =>
    if hU : h ∈ localUniverse H d then (L6 h hU).choose else ∅
  have hAw : ∀ h (hU : h ∈ localUniverse H d), Aw h = (L6 h hU).choose :=
    fun h hU => dif_pos hU
  refine ⟨Aw, ?_, ?_⟩
  · intro h hU
    obtain ⟨h1, h2, h3, -⟩ := (L6 h hU).choose_spec
    rw [← hAw h hU] at h1 h2 h3
    have hne : (restrictCls H h (Aw h)).Nonempty := by
      by_contra hc
      unfold ldimBot at h2
      rw [if_neg hc] at h2
      exact WithBot.bot_ne_coe h2
    refine ⟨h1, hne, ?_, h3⟩
    unfold ldimBot at h2
    rw [if_pos hne] at h2
    exact_mod_cast h2
  · intro h hU
    rw [hAw h hU]
    exact (L6 h hU).choose_spec.2.2.2

end MoranYanPAC.Dev.Goal.PartA
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
/-! ## Stubs (each proved in a Part) -/
alias exists_sourceWitnesses := MoranYanPAC.Dev.Goal.PartA.exists_sourceWitnesses

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartC
open MoranYanPAC.Main MoranYanPAC.Learner
/-- A shattered finite set of size `k` yields a shattered tree of depth `k`. -/
theorem card_le_ldim_of_shatters {X : Type*} (U : Set (X → Bool)) (C : Finset X)
    (hC : UnderstandingML.Shatters U C) : (C.card : ℕ∞) ≤ UnderstandingML.ldim U := by
  rcases C.eq_empty_or_nonempty with h0 | ⟨x0, _⟩
  · subst h0; simp
  classical
  let e : Fin C.card ≃ C := C.equivFin.symm
  let v : List Bool → X := fun l => if h : l.length < C.card then (e ⟨l.length, h⟩ : X) else x0
  have hv : UnderstandingML.ShattersTree U C.card v := by
    intro y
    obtain ⟨h, hU, hh⟩ := hC (fun c => y (e.symm c))
    refine ⟨h, hU, fun t => ?_⟩
    have hlen : (List.ofFn (fun j : Fin (t : ℕ) ↦ y ⟨j, lt_trans j.2 t.2⟩)).length = t :=
      List.length_ofFn
    have hvt : v (List.ofFn (fun j : Fin (t : ℕ) ↦ y ⟨j, lt_trans j.2 t.2⟩)) = (e t : X) := by
      simp only [v, hlen, t.2, dif_pos]
    rw [hvt, hh (e t)]
    simp
  unfold UnderstandingML.ldim
  exact le_iSup₂ (f := fun (k : ℕ) (_ : ∃ v : List Bool → X, UnderstandingML.ShattersTree U k v) =>
    (k : ℕ∞)) C.card ⟨v, hv⟩

theorem vcDim_localUniverse_le {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) :
    UnderstandingML.vcDim (PrivLittlestone.localUniverse H d) ≤ d := by
  have h4 := (dimension_decreases_with_rank H d hH hd hd1).2
  have hU : UnderstandingML.ldim (PrivLittlestone.localUniverse H d) = d := by
    unfold UnderstandingML.ldimBot at h4
    split_ifs at h4 with hne
    · exact_mod_cast h4
    · exact absurd h4 (WithBot.bot_ne_coe)
  unfold UnderstandingML.vcDim
  refine iSup₂_le fun C hC => ?_
  rw [← hU]
  exact card_le_ldim_of_shatters _ C hC

end MoranYanPAC.Dev.Goal.PartC
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias vcDim_localUniverse_le := MoranYanPAC.Dev.Goal.PartC.vcDim_localUniverse_le

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartA
open MoranYanPAC.Main MoranYanPAC.Learner PrivLittlestone UnderstandingML
/-- Every candidate lies in the local universe. -/
theorem candidates_subset {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (Aw : (X → Bool) → Finset X) (S : List (X × Bool)) :
    candidates H d Aw S ⊆ PrivLittlestone.localUniverse H d := by
  intro g hg
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hg
  exact (PrivLittlestone.Dev.Sel.selDesc_prop H d Aw _ d g hv).1.1

end MoranYanPAC.Dev.Goal.PartA
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias candidates_subset := MoranYanPAC.Dev.Goal.PartA.candidates_subset

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartA
open MoranYanPAC.Main MoranYanPAC.Learner PrivLittlestone UnderstandingML
/-- The candidate set is finite (Lemma 11) and nonempty (Lemma 10). -/
theorem candidates_finite_nonempty {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw) (S : List (X × Bool)) :
    (candidates H d Aw S).Finite ∧ (candidates H d Aw S).Nonempty := by
  refine ⟨(global_local_candidate_counts H d hH hd hd1 Aw hAw S).2.1, ?_⟩
  obtain ⟨h, hh⟩ := id hH
  have hU : h ∈ localUniverse H d := fun A _ => ⟨h, hh, fun _ _ => rfl⟩
  let v : Fin S.length → Bool := fun i => h (S.get i).1
  have hV : h ∈ versionCell H d S v := ⟨hU, fun _ => rfl⟩
  obtain ⟨g, hg, -⟩ := PrivLittlestone.eq_21 H d hH hd hd1 Aw hAw.1 S v ⟨h, hV⟩ h hV
  exact ⟨g, Set.mem_iUnion.2 ⟨v, hg⟩⟩

end MoranYanPAC.Dev.Goal.PartA
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias candidates_finite_nonempty := MoranYanPAC.Dev.Goal.PartA.candidates_finite_nonempty

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartC
open MoranYanPAC.Main MoranYanPAC.Learner
/-- The support of a finite Gibbs law lies in its candidate set. -/
theorem finiteGibbs_support {Y : Type*} (out : Finset Y) (hne : out.Nonempty) (f : Y → ℝ) :
    ∀ h ∈ (finiteGibbs out hne f).support, h ∈ out := by
  intro h hh
  unfold finiteGibbs at hh
  obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
  exact a.2

theorem candidateOut_eq {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw) (S : List (X × Bool)) :
    ∀ h, h ∈ candidateOut H d Aw S ↔ h ∈ candidates H d Aw S := by
  intro h
  have hfn := candidates_finite_nonempty H d hH hd hd1 Aw hAw S
  unfold candidateOut
  rw [dif_pos hfn, Set.Finite.mem_toFinset]

theorem rankRange_le {X : Type*} (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (S : List (X × Bool)) : rankRange (candidateData H d Aw) S ≤ d := by
  classical
  unfold rankRange
  refine le_trans (Nat.sub_le _ _) ?_
  refine Finset.sup'_le _ _ fun h _ => ?_
  exact Nat.findGreatest_le d

/-- A candidate with no mistakes on a realizable sample. -/
theorem exists_perfect_candidate {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (S : List (X × Bool)) (hstar : X → Bool) (hstarH : hstar ∈ H)
    (hreal : ∀ z ∈ S, hstar z.1 = z.2) :
    ∃ g ∈ candidates H d Aw S, empiricalLoss S g = 0 := by
  have hstarU : hstar ∈ PrivLittlestone.localUniverse H d := by
    intro A _
    exact ⟨hstar, hstarH, fun _ _ => rfl⟩
  let v : Fin S.length → Bool := fun i => hstar (S.get i).1
  have hmem : hstar ∈ PrivLittlestone.versionCell H d S v := ⟨hstarU, fun i => rfl⟩
  obtain ⟨g, hg, -⟩ := PrivLittlestone.eq_21 H d hH hd hd1 Aw hAw.1 S v ⟨hstar, hmem⟩ hstar hmem
  refine ⟨g, Set.mem_iUnion.mpr ⟨v, hg⟩, ?_⟩
  have hgV : g ∈ PrivLittlestone.versionCell H d S v :=
    (PrivLittlestone.Dev.Sel.selDesc_prop H d Aw _ d g hg).1
  unfold empiricalLoss
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro z hz
  obtain ⟨i, rfl⟩ := List.get_of_mem hz
  have := hgV.2 i
  simp only [v] at this
  have h3 : g (S.get i).1 = (S.get i).2 := this.trans (hreal _ hz)
  simpa using h3

end MoranYanPAC.Dev.Goal.PartC
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartA
open MoranYanPAC.Main MoranYanPAC.Learner PrivLittlestone UnderstandingML
/-- Every output of the learner lies in `U` or is the constant `false`. -/
theorem learner_support {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (Aw : (X → Bool) → Finset X) (ε δ : ℝ) (S : List (X × Bool)) :
    ∀ h ∈ (littlestoneLearner H d Aw ε δ S).support,
      h ∈ PrivLittlestone.localUniverse H d ∨ h = fun _ => false := by
  intro h hh
  unfold littlestoneLearner structuralMechanism finiteGibbs at hh
  rw [PMF.support_map] at hh
  obtain ⟨g, -, rfl⟩ := hh
  have hg := g.2
  change g.1 ∈ candidateOut H d Aw S at hg
  unfold candidateOut at hg
  split_ifs at hg with hc
  · left
    exact candidates_subset H d Aw S (hc.1.mem_toFinset.1 hg)
  · right
    exact Finset.mem_singleton.1 hg

/-! ### Helpers for the structural axioms -/
theorem mem_candidateOut {X : Type*} {H : Set (X → Bool)} {d : ℕ}
    {Aw : (X → Bool) → Finset X} {S : List (X × Bool)}
    (hfin : (candidates H d Aw S).Finite ∧ (candidates H d Aw S).Nonempty) (g : X → Bool) :
    g ∈ candidateOut H d Aw S ↔ g ∈ candidates H d Aw S := by
  unfold candidateOut
  rw [dif_pos hfin]
  exact hfin.1.mem_toFinset

theorem loss_insert {X : Type*} (l r : List (X × Bool)) (u : X × Bool) (h : X → Bool) :
    (empiricalLoss (l ++ u :: r) h : ℝ) =
      empiricalLoss (l ++ r) h + (if h u.1 ≠ u.2 then 1 else 0) := by
  unfold empiricalLoss
  simp only [List.filter_append, List.filter_cons, List.length_append]
  split_ifs <;> simp_all; ring

theorem score_neighbor {X : Type*} (S T : List (X × Bool)) (hST : IsInsDelNeighbor S T)
    (h : X → Bool) :
    |((S.length : ℝ) - empiricalLoss S h) - ((T.length : ℝ) - empiricalLoss T h)| ≤ 1 := by
  rcases hST with ⟨l, r, u, rfl, rfl⟩ | ⟨l, r, u, rfl, rfl⟩
  · rw [loss_insert]
    simp only [List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rw [loss_insert]
    simp only [List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem neighbor_points {X : Type*} (S T : List (X × Bool)) (hST : IsInsDelNeighbor S T) :
    ∃ u : X × Bool, ∀ z ∈ S, z = u ∨ z ∈ T := by
  rcases hST with ⟨l, r, u, rfl, rfl⟩ | ⟨l, r, u, rfl, rfl⟩
  · refine ⟨u, fun z hz => Or.inr ?_⟩
    simp only [List.mem_append, List.mem_cons] at hz ⊢
    tauto
  · refine ⟨u, fun z hz => ?_⟩
    simp only [List.mem_append, List.mem_cons] at hz ⊢
    tauto

theorem loss_congr {X : Type*} (S : List (X × Bool)) {g h : X → Bool}
    (hag : ∀ z ∈ S, g z.1 = h z.1) : empiricalLoss S g = empiricalLoss S h := by
  unfold empiricalLoss
  congr 1
  apply List.filter_congr
  intro z hz
  rw [hag z hz]

theorem exists_F {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw) (T : List (X × Bool))
    (g : X → Bool) (hgU : g ∈ localUniverse H d) :
    ∃ h, h ∈ candidates H d Aw T ∧ (g ∈ candidates H d Aw T → h = g) ∧
      (g ∉ candidates H d Aw T → rankOf H d g < rankOf H d h ∧
        g ∈ witnessSpace H d Aw h ∧ ∀ z ∈ T, h z.1 = g z.1) := by
  by_cases hg : g ∈ candidates H d Aw T
  · exact ⟨g, hg, fun _ => rfl, fun h => absurd hg h⟩
  let v : Fin T.length → Bool := fun i => g (T.get i).1
  have hgV : g ∈ versionCell H d T v := ⟨hgU, fun _ => rfl⟩
  obtain ⟨h, hhD, hW, -, hlt⟩ := PrivLittlestone.eq_21 H d hH hd hd1 Aw hAw.1 T v ⟨g, hgV⟩ g hgV
  have hgD : g ∉ selD H d Aw (versionCell H d T v) := fun hD => hg (Set.mem_iUnion.2 ⟨v, hD⟩)
  have hhV := (PrivLittlestone.Dev.Sel.selDesc_prop H d Aw _ d h hhD).1
  refine ⟨h, Set.mem_iUnion.2 ⟨v, hhD⟩, fun h' => absurd h' hg, fun _ => ⟨hlt hgD, hW, ?_⟩⟩
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hz
  exact hhV.2 i

theorem count_bound {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw) (S : List (X × Bool))
    (u : X × Bool) (h : X → Bool) (hhU : h ∈ localUniverse H d) (t : ℕ)
    (ht : t ≤ rankOf H d h) (G : Set (X → Bool))
    (hG : ∀ g ∈ G, g ∈ candidates H d Aw S ∧ g ∈ witnessSpace H d Aw h ∧
      (∀ z ∈ S, z = u ∨ h z.1 = g z.1) ∧ rankOf H d g + t = rankOf H d h) :
    G.encard ≤ ((2 * (2 * (d + 1)) ^ t : ℕ) : ℕ∞) := by
  classical
  set s := rankOf H d h - t with hs
  let w : Bool → Fin S.length → Bool := fun b i =>
    if (S.get i).1 = u.1 then b else h (S.get i).1
  let A : Bool → Set (X → Bool) := fun b =>
    selT H d Aw (versionCell H d S (w b)) s ∩ witnessSpace H d Aw h
  have hsub : G ⊆ A false ∪ A true := by
    intro g hg
    obtain ⟨hgc, hgW, hgpts, hgr⟩ := hG g hg
    obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hgc
    have hvV := (PrivLittlestone.Dev.Sel.selDesc_prop H d Aw _ d g hv).1
    have hvw : v = w (g u.1) := by
      funext i
      rw [← hvV.2 i]
      simp only [w]
      split_ifs with hx
      · rw [hx]
      · rcases hgpts (S.get i) (List.get_mem _ _) with he | he
        · exact absurd (by rw [he]) hx
        · exact he.symm
    rw [hvw] at hv
    have hT := MoranYanPAC.Dev.L11a.selD_sub_union H d Aw _ hv
    simp only [Set.mem_iUnion] at hT
    obtain ⟨s', -, hs'⟩ := hT
    have hrs : s' = s := by
      have := hs'.2.1
      omega
    rw [hrs] at hs'
    have hmem : g ∈ A (g u.1) := ⟨hs', hgW⟩
    cases hb : g u.1
    · rw [hb] at hmem; exact Or.inl hmem
    · rw [hb] at hmem; exact Or.inr hmem
  have hA : ∀ b, (A b).encard ≤ (((2 * (d + 1)) ^ t : ℕ) : ℕ∞) := by
    intro b
    rcases (A b).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he, Set.encard_empty]; exact bot_le
    have hne : (versionCell H d S (w b)).Nonempty := ⟨x, hx.1.1⟩
    have := ((global_local_candidate_counts H d hH hd hd1 Aw hAw S).1 (w b) hne).2 h hhU s
      (Nat.sub_le _ _)
    have hts : rankOf H d h - s = t := by omega
    rwa [hts] at this
  calc G.encard ≤ (A false ∪ A true).encard := Set.encard_le_encard hsub
    _ ≤ (A false).encard + (A true).encard := Set.encard_union_le _ _
    _ ≤ (((2 * (d + 1)) ^ t : ℕ) : ℕ∞) + (((2 * (d + 1)) ^ t : ℕ) : ℕ∞) := add_le_add (hA _) (hA _)
    _ = ((2 * (2 * (d + 1)) ^ t : ℕ) : ℕ∞) := by push_cast; ring

theorem nat_bound (d t : ℕ) (ht : 1 ≤ t) :
    2 * (2 * (d + 1)) ^ t ≤ (4 * (d + 1)) ^ t := by
  have h4 : 4 * (d + 1) = 2 * (2 * (d + 1)) := by ring
  rw [h4, mul_pow 2 (2 * (d + 1)) t]
  apply Nat.mul_le_mul_right
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht

/-- Section 7.3: the four axioms with `Δ = 1`, `B = 4(d+1)`. -/
theorem structuralAxioms_candidateData {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw) :
    StructuralAxioms (candidateData H d Aw) 1 (4 * ((d : ℝ) + 1)) := by
  classical
  have hout : ∀ S g, g ∈ candidateOut H d Aw S ↔ g ∈ candidates H d Aw S := fun S g =>
    mem_candidateOut (candidates_finite_nonempty H d hH hd hd1 Aw hAw S) g
  intro S T hST
  refine ⟨fun h => score_neighbor S T hST h, ?_⟩
  have hex : ∀ g : {g // g ∈ (candidateData H d Aw).out S}, ∃ h,
      h ∈ candidates H d Aw T ∧ (g.1 ∈ candidates H d Aw T → h = g.1) ∧
      (g.1 ∉ candidates H d Aw T → rankOf H d g.1 < rankOf H d h ∧
        g.1 ∈ witnessSpace H d Aw h ∧ ∀ z ∈ T, h z.1 = g.1 z.1) := fun g =>
    exists_F H d hH hd hd1 Aw hAw T g.1
      (candidates_subset H d Aw S ((hout S g.1).1 g.2))
  choose Fv hFv using hex
  let F : {g // g ∈ (candidateData H d Aw).out S} → {h // h ∈ (candidateData H d Aw).out T} :=
    fun g => ⟨Fv g, (hout T _).2 (hFv g).1⟩
  refine ⟨F, fun g => ⟨fun hg => (hFv g).2.1 ((hout T _).1 hg),
    fun hg => ((hFv g).2.2 (fun h' => hg ((hout T _).2 h'))).1⟩, ?_, ?_⟩
  · intro h t ht
    let Pre := {g : {g // g ∈ (candidateData H d Aw).out S} | (F g).val = h.val ∧
        (candidateData H d Aw).rank g.val + t = (candidateData H d Aw).rank h.val}
    have hhc : h.1 ∈ candidates H d Aw T := (hout T _).1 h.2
    have hhU := candidates_subset H d Aw T hhc
    obtain ⟨u, hu⟩ := neighbor_points S T hST
    have hPre : Pre.encard ≤ ((2 * (2 * (d + 1)) ^ t : ℕ) : ℕ∞) := by
      by_cases hrt : t ≤ rankOf H d h.1
      · rw [← Subtype.val_injective.encard_image]
        apply count_bound H d hH hd hd1 Aw hAw S u h.1 hhU t hrt
        rintro _ ⟨g, ⟨hFg, hrk⟩, rfl⟩
        change rankOf H d g.1 + t = rankOf H d h.1 at hrk
        have hgc : g.1 ∉ candidates H d Aw T := by
          intro hc
          have := (hFv g).2.1 hc
          change Fv g = h.1 at hFg
          rw [hFg] at this
          rw [this] at hrk
          omega
        obtain ⟨-, hW, hpts⟩ := (hFv g).2.2 hgc
        change Fv g = h.1 at hFg
        rw [hFg] at hW hpts
        refine ⟨(hout S _).1 g.2, hW, fun z hz => ?_, hrk⟩
        rcases hu z hz with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (hpts z h1)
      · have : Pre = ∅ := by
          ext g
          simp only [Set.mem_empty_iff_false, iff_false]
          rintro ⟨-, hrk⟩
          change rankOf H d g.1 + t = rankOf H d h.1 at hrk
          omega
        rw [this, Set.encard_empty]
        exact bot_le
    have h1 : ((Pre.encard : ℕ∞) : ENNReal) ≤ (((2 * (2 * (d + 1)) ^ t : ℕ) : ℕ∞) : ENNReal) :=
      ENat.toENNReal_le.2 hPre
    have h2 : ENNReal.ofReal ((4 * ((d : ℝ) + 1)) ^ t) = (((4 * (d + 1)) ^ t : ℕ) : ENNReal) := by
      rw [← ENNReal.ofReal_natCast]
      push_cast
      rfl
    refine h1.trans ?_
    rw [h2, ENat.toENNReal_coe]
    exact_mod_cast nat_bound d t ht
  · intro g
    change |((S.length : ℝ) - empiricalLoss S g.1) - ((T.length : ℝ) - empiricalLoss T (Fv g))| ≤ 1
    by_cases hg : g.1 ∈ candidates H d Aw T
    · rw [(hFv g).2.1 hg]
      exact score_neighbor S T hST g.1
    · obtain ⟨-, -, hpts⟩ := (hFv g).2.2 hg
      rw [loss_congr T hpts]
      exact score_neighbor S T hST g.1

end MoranYanPAC.Dev.Goal.PartA
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias structuralAxioms_candidateData := MoranYanPAC.Dev.Goal.PartA.structuralAxioms_candidateData

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartC
open MoranYanPAC.Main MoranYanPAC.Learner
theorem learner_utility {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (S : List (X × Bool)) (hstar : X → Bool) (hstarH : hstar ∈ H)
    (hreal : ∀ z ∈ S, hstar z.1 = z.2) (hdS : d ≤ S.length) (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    ENNReal.ofReal (1 - β) ≤ eventProbability (littlestoneLearner H d Aw ε δ S)
      {h | h ∈ PrivLittlestone.localUniverse H d ∧ (empiricalLoss S h : ℝ) ≤
        (2 / ε) * ((d : ℝ) * Real.log (64 * ((d : ℝ) + 1) / δ) +
          Real.log (2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * S.length / d) ^ d / β))} := by
  have hax := structuralAxioms_candidateData H d hH hd hd1 Aw hAw
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hB : (1 : ℝ) ≤ 4 * ((d : ℝ) + 1) := by linarith
  have hu := (structural_exponential_mechanism (candidateData H d Aw) ε δ 1 (4 * ((d : ℝ) + 1))
    hε hε1 hδ hδ1 one_pos hB hax).2 S β hβ hβ1
  refine hu.trans ?_
  unfold eventProbability
  refine le_trans (le_of_eq (PMF.toOuterMeasure_apply_inter_support _ _).symm)
    (MeasureTheory.OuterMeasure.mono _ ?_)
  rintro h ⟨hscore, hsupp⟩
  set M := candidateData H d Aw with hM
  have hout : h ∈ M.out S := finiteGibbs_support _ _ _ h hsupp
  have hcand : h ∈ candidates H d Aw S := (candidateOut_eq H d hH hd hd1 Aw hAw S h).mp hout
  refine ⟨candidates_subset H d Aw S hcand, ?_⟩
  simp only [Set.mem_ofPred_eq] at hscore
  -- best score is `|S|`
  obtain ⟨g, hg, hg0⟩ := exists_perfect_candidate H d hH hd hd1 Aw hAw S hstar hstarH hreal
  have hgout : g ∈ M.out S := (candidateOut_eq H d hH hd hd1 Aw hAw S g).mpr hg
  have hbest : (S.length : ℝ) ≤ bestScore M S := by
    have := Finset.le_sup' (M.score S) hgout
    unfold bestScore
    refine le_trans (le_of_eq ?_) this
    simp [M, candidateData, hg0]
  have hsc : M.score S h = (S.length : ℝ) - (empiricalLoss S h : ℝ) := rfl
  -- the rank term
  have hrr : (rankRange M S : ℝ) ≤ d := by exact_mod_cast rankRange_le H d Aw S
  have hlog1 : Real.log (16 * (4 * ((d : ℝ) + 1)) / δ) = Real.log (64 * ((d : ℝ) + 1) / δ) := by
    ring_nf
  have hlog1pos : 0 ≤ Real.log (64 * ((d : ℝ) + 1) / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    nlinarith
  have hT1 : (rankRange M S : ℝ) * Real.log (16 * (4 * ((d : ℝ) + 1)) / δ) ≤
      d * Real.log (64 * ((d : ℝ) + 1) / δ) := by
    rw [hlog1]; exact mul_le_mul_of_nonneg_right hrr hlog1pos
  -- the count term
  have hcard : ((M.out S).card : ℝ) ≤
      2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * S.length / d) ^ d := by
    have h11 := (global_local_candidate_counts H d hH hd hd1 Aw hAw S).2.2 hdS
    refine le_trans (le_of_eq ?_) h11
    have hfn := candidates_finite_nonempty H d hH hd hd1 Aw hAw S
    have : M.out S = hfn.1.toFinset := by
      show candidateOut H d Aw S = _
      unfold candidateOut
      rw [dif_pos hfn]
    rw [this, Set.ncard_eq_toFinset_card _ hfn.1]
  have hcardpos : (0 : ℝ) < (M.out S).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨h, hout⟩
  have hT2 : Real.log ((M.out S).card / β) ≤
      Real.log (2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * S.length / d) ^ d / β) :=
    Real.log_le_log (div_pos hcardpos hβ) (div_le_div_of_nonneg_right hcard hβ.le)
  have hQ : (2 * 1 / ε) * ((rankRange M S : ℝ) * Real.log (16 * (4 * ((d : ℝ) + 1)) / δ) +
      Real.log ((M.out S).card / β)) ≤
      (2 / ε) * ((d : ℝ) * Real.log (64 * ((d : ℝ) + 1) / δ) +
        Real.log (2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * S.length / d) ^ d / β)) := by
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [hsc] at hscore
  linarith

end MoranYanPAC.Dev.Goal.PartC
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias learner_utility := MoranYanPAC.Dev.Goal.PartC.learner_utility

alias learner_support := MoranYanPAC.Dev.Goal.PartA.learner_support

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartB
open MoranYanPAC.Main MoranYanPAC.Learner
/-- Expansion of the main logarithm. -/
theorem log_main_eq (d : ℕ) (α β ε δ : ℝ) (hd1 : 1 ≤ d)
    (hα : 0 < α) (hε : 0 < ε) (hδ : 0 < δ) :
    (d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) + Real.log (1 / β) =
      (d : ℝ) * (Real.log d - Real.log α - Real.log ε - Real.log δ) - Real.log β := by
  have hd : (0 : ℝ) < d := by exact_mod_cast hd1
  rw [Real.log_div hd.ne' (by positivity), Real.log_mul (by positivity) hδ.ne',
    Real.log_mul hα.ne' hε.ne', one_div, Real.log_inv]
  ring

theorem small_case (d : ℕ) (hd1 : 1 ≤ d) (α β ε δ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hL : (d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) + Real.log (1 / β) < Real.log 2) :
    1 / 2 < α ∧ 1 / 2 < β := by
  rw [log_main_eq d α β ε δ hd1 hα hε hδ] at hL
  have hla : Real.log α < 0 := Real.log_neg hα hα1
  have hlb : Real.log β < 0 := Real.log_neg hβ hβ1
  have hle : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hlδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hd1' : d = 1 := by
    by_contra hne
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    have hld2 : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
    have h1 : 2 * Real.log 2 ≤ (d : ℝ) * Real.log d := by nlinarith
    have h2 : 0 ≤ (d : ℝ) * (- Real.log α - Real.log ε - Real.log δ) := by
      apply mul_nonneg (by linarith); linarith
    nlinarith
  subst hd1'
  simp only [Nat.cast_one, Real.log_one, one_mul] at hL
  have hhalf : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
  constructor
  · rw [← Real.log_lt_log_iff (by norm_num) hα, hhalf]; linarith
  · rw [← Real.log_lt_log_iff (by norm_num) hβ, hhalf]; linarith

/-- `log m ≤ m c − 1 − log c`. -/
theorem log_le_lin (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Real.log m ≤ m * c - 1 - Real.log c := by
  have h := Real.log_le_sub_one_of_pos (mul_pos hm hc)
  rw [Real.log_mul hm.ne' hc.ne'] at h
  linarith

theorem arith (Cvc : ℝ) (hCvc : 0 < Cvc) (d : ℕ) (hd1 : 1 ≤ d) (α β ε δ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (n : ℕ)
    (hL : Real.log 2 ≤ (d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) + Real.log (1 / β))
    (hn : (120 + 5 * Cvc) * ((d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) + Real.log (1 / β)) /
      (α * ε) ≤ n) :
    d ≤ n ∧
    Cvc * ((d : ℝ) * Real.log (Real.exp 1 / α) + Real.log (1 / (β / 2))) / α ≤ n ∧
    (2 / ε) * ((d : ℝ) * Real.log (64 * ((d : ℝ) + 1) / δ) +
      Real.log (2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * n / d) ^ d / (β / 2))) ≤ α / 2 * n := by
  rw [log_main_eq d α β ε δ hd1 hα hε hδ] at hL hn
  set L0 := (d : ℝ) * (Real.log d - Real.log α - Real.log ε - Real.log δ) - Real.log β with hL0
  have hla : Real.log α < 0 := Real.log_neg hα hα1
  have hlb : Real.log β < 0 := Real.log_neg hβ hβ1
  have hle : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hlδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hP1 : 0 ≤ (d : ℝ) * Real.log d := mul_nonneg (by linarith) hld
  have hP2 : 0 ≤ (d : ℝ) * (- Real.log α) := mul_nonneg (by linarith) (by linarith)
  have hP3 : 0 ≤ (d : ℝ) * (- Real.log ε) := mul_nonneg (by linarith) (by linarith)
  have hP4 : 0 ≤ (d : ℝ) * (- Real.log δ) := mul_nonneg (by linarith) (by linarith)
  -- `d log 2 ≤ L0`
  have hdl2 : (d : ℝ) * Real.log 2 ≤ L0 := by
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 1 := by omega
      subst this
      simp only [Nat.cast_one, one_mul] at hL ⊢
      linarith
    · have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast h
      have hld2 : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have : (d : ℝ) * Real.log 2 ≤ (d : ℝ) * Real.log d :=
        mul_le_mul_of_nonneg_left hld2 (by linarith)
      linarith
  have hL0pos : 0 ≤ L0 := le_trans (by positivity) hdl2
  have hαε : 0 < α * ε := mul_pos hα hε
  have hαε1 : α * ε ≤ 1 := mul_le_one₀ hα1.le hε.le hε1
  have hn' : (120 + 5 * Cvc) * L0 ≤ n * (α * ε) := (div_le_iff₀ hαε).mp hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnαε : (n : ℝ) * (α * ε) ≤ n := mul_le_of_le_one_right hn0 hαε1
  have hCL : 0 ≤ Cvc * L0 := mul_nonneg hCvc.le hL0pos
  have hn120 : 120 * L0 ≤ n * (α * ε) := by nlinarith
  have hdn : (d : ℝ) ≤ n := by nlinarith
  refine ⟨by exact_mod_cast hdn, ?_, ?_⟩
  · -- (ii)
    rw [div_le_iff₀ hα]
    have hY : (d : ℝ) * Real.log (Real.exp 1 / α) + Real.log (1 / (β / 2)) ≤ 5 * L0 := by
      rw [Real.log_div (Real.exp_pos 1).ne' hα.ne', Real.log_exp,
        Real.log_div one_ne_zero (by positivity), Real.log_div hβ.ne' two_ne_zero, Real.log_one]
      nlinarith
    have h1 : Cvc * ((d : ℝ) * Real.log (Real.exp 1 / α) + Real.log (1 / (β / 2))) ≤
        Cvc * (5 * L0) := mul_le_mul_of_nonneg_left hY hCvc.le
    have h2 : (n : ℝ) * (α * ε) ≤ n * α := by
      apply mul_le_mul_of_nonneg_left _ hn0
      nlinarith
    nlinarith
  · -- (iii)
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by linarith) hdn
    have hdpos : (0 : ℝ) < d := by linarith
    have hX : (d : ℝ) * Real.log (64 * ((d : ℝ) + 1) / δ) +
        Real.log (2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * n / d) ^ d / (β / 2)) ≤
        α * ε * n / 4 := by
      have e1 : Real.log (64 * ((d : ℝ) + 1) / δ) =
          6 * Real.log 2 + Real.log ((d : ℝ) + 1) - Real.log δ := by
        rw [Real.log_div (by positivity) hδ.ne', Real.log_mul (by norm_num) (by positivity),
          show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
        push_cast; ring
      have e2 : Real.log (2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * n / d) ^ d / (β / 2)) =
          Real.log 2 + d * (Real.log 2 + Real.log ((d : ℝ) + 1)) +
            d * (1 + Real.log n - Real.log d) - (Real.log β - Real.log 2) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
          Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) hdpos.ne',
          Real.log_mul (Real.exp_pos 1).ne' hnpos.ne', Real.log_exp,
          Real.log_div hβ.ne' two_ne_zero]
      rw [e1, e2]
      have hd1l : Real.log ((d : ℝ) + 1) ≤ Real.log 2 + Real.log d := by
        rw [← Real.log_mul two_ne_zero hdpos.ne']
        exact Real.log_le_log (by positivity) (by linarith)
      have hQ1 : (d : ℝ) * Real.log ((d : ℝ) + 1) ≤ d * (Real.log 2 + Real.log d) :=
        mul_le_mul_of_nonneg_left hd1l hdpos.le
      -- the key estimate on `log (n / d)`
      have hkey : Real.log n - Real.log d ≤
          (n / d) * (α * ε / 16) - 1 - (Real.log α + Real.log ε - 4 * Real.log 2) := by
        have h := log_le_lin (n / d) (α * ε / 16) (by positivity) (by positivity)
        rw [Real.log_div hnpos.ne' hdpos.ne', Real.log_div (by positivity) (by norm_num),
          Real.log_mul hα.ne' hε.ne', show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at h
        push_cast at h
        linarith
      have hQ2 : (d : ℝ) * (Real.log n - Real.log d) ≤
          d * ((n / d) * (α * ε / 16) - 1 - (Real.log α + Real.log ε - 4 * Real.log 2)) :=
        mul_le_mul_of_nonneg_left hkey hdpos.le
      have hQ3 : (d : ℝ) * ((n / d) * (α * ε / 16)) = α * ε * n / 16 := by
        field_simp
      have hl2L : Real.log 2 ≤ L0 := by linarith
      have hL0e : L0 = (d : ℝ) * Real.log d + d * (- Real.log α) + d * (- Real.log ε) +
          d * (- Real.log δ) - Real.log β := by rw [hL0]; ring
      have hQ2' : (d : ℝ) * Real.log n - d * Real.log d ≤
          α * ε * n / 16 - d - d * Real.log α - d * Real.log ε + 4 * (d * Real.log 2) := by
        have := hQ2
        rw [mul_sub, mul_sub, mul_sub, mul_sub, hQ3, mul_one, mul_add] at this
        linarith
      have hring : (d : ℝ) * (6 * Real.log 2 + Real.log ((d : ℝ) + 1) - Real.log δ) +
          (Real.log 2 + d * (Real.log 2 + Real.log ((d : ℝ) + 1)) +
            d * (1 + Real.log n - Real.log d) - (Real.log β - Real.log 2)) =
          7 * (d * Real.log 2) + 2 * (d * Real.log ((d : ℝ) + 1)) + d * (- Real.log δ) +
            2 * Real.log 2 + d + (d * Real.log n - d * Real.log d) - Real.log β := by ring
      rw [hring]
      linarith
    calc (2 / ε) * ((d : ℝ) * Real.log (64 * ((d : ℝ) + 1) / δ) +
          Real.log (2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * n / d) ^ d / (β / 2)))
        ≤ (2 / ε) * (α * ε * n / 4) := mul_le_mul_of_nonneg_left hX (by positivity)
      _ = α / 2 * n := by field_simp; ring

end MoranYanPAC.Dev.Goal.PartB
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias arith := MoranYanPAC.Dev.Goal.PartB.arith

alias small_case := MoranYanPAC.Dev.Goal.PartB.small_case

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartB
open MoranYanPAC.Main MoranYanPAC.Learner
theorem vcSuccessEvent_measurable {X : Type*} [MeasurableSpace X]
    (G : Set (X → Bool)) (P : Measure (X × Bool)) (hG : VCEventsMeasurable G P) (α : ℝ) (n : ℕ) :
    MeasurableSet (vcSuccessEvent G P α n) := by
  have h := (hG.2.1 n (α / 2) α).compl
  convert h using 1
  ext s
  simp only [vcSuccessEvent, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]

theorem lower_bound {X : Type*} [MeasurableSpace X]
    (A : List (X × Bool) → PMF (X → Bool)) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (G : Set (X → Bool)) (hG : VCEventsMeasurable G P) (hstar : X → Bool) (hstarG : hstar ∈ G)
    (hreal : ∀ᵐ z ∂P, hstar z.1 = z.2) (α β1 β2 : ℝ) (n : ℕ)
    (hvc : ENNReal.ofReal (1 - β1) ≤ sampleLaw P n (vcSuccessEvent G P α n))
    (hA : ∀ s : Fin n → X × Bool, (∀ i, hstar (s i).1 = (s i).2) →
      ENNReal.ofReal (1 - β2) ≤ eventProbability (A (List.ofFn s))
        {h | h ∈ G ∧ empiricalRate (List.ofFn s) h ≤ α / 2}) :
    ENNReal.ofReal (1 - β1) * ENNReal.ofReal (1 - β2) ≤ pacSuccessProbability A P α n := by
  have hRae : ∀ᵐ s ∂(sampleLaw P n), ∀ i, hstar (s i).1 = (s i).2 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P) (i := i)).eventually hreal
  set c := ENNReal.ofReal (1 - β2)
  have hpt : ∀ᵐ s ∂(sampleLaw P n), (vcSuccessEvent G P α n).indicator (fun _ => c) s ≤
      conditionalSuccess A P α (List.ofFn s) := by
    filter_upwards [hRae] with s hs
    by_cases hsv : s ∈ vcSuccessEvent G P α n
    · rw [Set.indicator_of_mem hsv]
      refine (hA s hs).trans (MeasureTheory.OuterMeasure.mono _ ?_)
      intro h ⟨hG', hle⟩
      exact hsv h hG' hle
    · rw [Set.indicator_of_notMem hsv]
      exact zero_le
  unfold pacSuccessProbability
  calc ENNReal.ofReal (1 - β1) * c ≤ c * sampleLaw P n (vcSuccessEvent G P α n) := by
        rw [mul_comm]; exact mul_le_mul_right hvc c
    _ = ∫⁻ s, (vcSuccessEvent G P α n).indicator (fun _ => c) s ∂(sampleLaw P n) :=
        (lintegral_indicator_const (vcSuccessEvent_measurable G P hG α n) c).symm
    _ ≤ _ := lintegral_mono_ae hpt

end MoranYanPAC.Dev.Goal.PartB
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias lower_bound := MoranYanPAC.Dev.Goal.PartB.lower_bound

/-- The trivial learner: a fair coin between the two constant predictors. -/
noncomputable def coinLearner (X : Type*) : List (X × Bool) → PMF (X → Bool) :=
  fun _ => (PMF.uniformOfFintype Bool).map (fun b => fun _ => b)

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartB
open MoranYanPAC.Main MoranYanPAC.Learner
theorem coinLearner_private (X : Type*) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Private (coinLearner X) ε δ := by
  intro S T _ E
  have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp ε) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε.le)
  calc eventProbability (coinLearner X S) E = 1 * eventProbability (coinLearner X T) E := by
        rw [one_mul]; rfl
    _ ≤ ENNReal.ofReal (Real.exp ε) * eventProbability (coinLearner X T) E :=
        mul_le_mul_left h1 _
    _ ≤ _ := le_add_right le_rfl

end MoranYanPAC.Dev.Goal.PartB
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias coinLearner_private := MoranYanPAC.Dev.Goal.PartB.coinLearner_private

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal.PartB
open MoranYanPAC.Main MoranYanPAC.Learner
/-- One of the two constant predictors has loss at most `1/2`. -/
theorem exists_const_good {X : Type*} [MeasurableSpace X] (P : Measure (X × Bool))
    [IsProbabilityMeasure P] : ∃ b : Bool, populationLoss P (fun _ => b) ≤ 1 / 2 := by
  have hm : ∀ b : Bool, MeasurableSet {z : X × Bool | b ≠ z.2} := fun b =>
    (MeasurableSet.of_discrete : MeasurableSet {y : Bool | b ≠ y}).preimage measurable_snd
  have hdisj : Disjoint {z : X × Bool | false ≠ z.2} {z : X × Bool | true ≠ z.2} := by
    rw [Set.disjoint_left]
    intro z h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    cases z.2 <;> simp_all
  have hun : {z : X × Bool | false ≠ z.2} ∪ {z : X × Bool | true ≠ z.2} = Set.univ := by
    ext z; simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    cases z.2 <;> simp
  have hsum := measure_union (μ := P) hdisj (hm true)
  rw [hun, measure_univ] at hsum
  have hsum' : populationLoss P (fun _ => false) + populationLoss P (fun _ => true) = 1 := by
    unfold populationLoss
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← hsum]
    simp
  by_cases h : populationLoss P (fun _ => false) ≤ 1 / 2
  · exact ⟨false, h⟩
  · exact ⟨true, by linarith⟩

theorem coinLearner_success {X : Type*} [MeasurableSpace X] (P : Measure (X × Bool))
    [IsProbabilityMeasure P] (α β : ℝ) (hα : 1 / 2 < α) (hβ : 1 / 2 < β) (n : ℕ) :
    PACExperimentMeasurable (coinLearner X) P α n ∧
      ENNReal.ofReal (1 - β) ≤ pacSuccessProbability (coinLearner X) P α n := by
  have hconst : (fun s : Fin n → X × Bool => conditionalSuccess (coinLearner X) P α (List.ofFn s)) =
      fun _ => conditionalSuccess (coinLearner X) P α [] := rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro S h hh
    unfold coinLearner at hh
    obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
    exact (MeasurableSet.of_discrete : MeasurableSet {y : Bool | b ≠ y}).preimage measurable_snd
  · rw [hconst]; exact aemeasurable_const
  · have : IsProbabilityMeasure (sampleLaw P n) := by
      unfold sampleLaw UnderstandingML.iidLaw; infer_instance
    obtain ⟨b, hb⟩ := exists_const_good P
    have hc : (2 : ENNReal)⁻¹ ≤ conditionalSuccess (coinLearner X) P α [] := by
      unfold conditionalSuccess eventProbability coinLearner
      rw [PMF.toOuterMeasure_map_apply]
      calc (2 : ENNReal)⁻¹ = (PMF.uniformOfFintype Bool).toOuterMeasure {b} := by
            rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
            simp
        _ ≤ _ := by
            apply MeasureTheory.OuterMeasure.mono
            intro b' hb'
            rw [Set.mem_singleton_iff] at hb'
            subst hb'
            show populationLoss P (fun _ => b') ≤ α
            linarith
    unfold pacSuccessProbability
    rw [hconst, lintegral_const, measure_univ, mul_one]
    refine le_trans ?_ hc
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end MoranYanPAC.Dev.Goal.PartB
end

section
set_option autoImplicit false
open MeasureTheory
namespace MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
alias coinLearner_success := MoranYanPAC.Dev.Goal.PartB.coinLearner_success

/-! ## Assembly -/
theorem private_pac_nearly_linear_dev :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [MeasurableSpace X]
      (H : Set (X → Bool)) (d : ℕ), H.Nonempty →
      UnderstandingML.ldim H = d → 1 ≤ d →
      ∀ (α β ε δ : ℝ), 0 < α → α < 1 → 0 < β → β < 1 →
        0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
      ∃ A : List (X × Bool) → PMF (X → Bool), Private A ε δ ∧
        ∀ P : Measure (X × Bool), IsProbabilityMeasure P →
          VCEventsMeasurable (PrivLittlestone.localUniverse H d) P → Realizable H P →
          ∀ n : ℕ,
            ⌈C * ((d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) +
              Real.log (1 / β)) / (α * ε)⌉₊ ≤ n →
            PACExperimentMeasurable A P α n ∧
            ENNReal.ofReal (1 - β) ≤ pacSuccessProbability A P α n := by
  obtain ⟨Cvc, hCvc, hvc⟩ := vc_generalization
  refine ⟨120 + 5 * Cvc, by positivity, ?_⟩
  intro X _ H d hH hd hd1 α β ε δ hα hα1 hβ hβ1 hε hε1 hδ hδ1
  by_cases hsmall : (d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) + Real.log (1 / β) < Real.log 2
  · obtain ⟨hα2, hβ2⟩ := small_case d hd1 α β ε δ hα hα1 hβ hβ1 hε hε1 hδ hδ1 hsmall
    refine ⟨coinLearner X, coinLearner_private X ε δ hε hδ, ?_⟩
    intro P hP _ _ n _
    exact coinLearner_success P α β hα2 hβ2 n
  push Not at hsmall
  obtain ⟨Aw, hAw⟩ := exists_sourceWitnesses H d hH hd hd1
  have hax := structuralAxioms_candidateData H d hH hd hd1 Aw hAw
  have hB : (1 : ℝ) ≤ 4 * ((d : ℝ) + 1) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨littlestoneLearner H d Aw ε δ,
    (structural_exponential_mechanism (candidateData H d Aw) ε δ 1 (4 * ((d : ℝ) + 1))
      hε hε1 hδ hδ1 one_pos hB hax).1, ?_⟩
  intro P hP hPm hR n hn
  have hn' : (120 + 5 * Cvc) * ((d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) + Real.log (1 / β)) /
      (α * ε) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  obtain ⟨hdn, hvcn, harith⟩ := arith Cvc hCvc d hd1 α β ε δ hα hα1 hβ hβ1 hε hε1 hδ hδ1 n hsmall hn'
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) hdn
  refine ⟨⟨?_, MoranYanPAC.Learner.conditionalSuccess_aemeasurable H d hH hd hd1 Aw hAw α ε δ hα hα1 hε hε1 hδ hδ1
    P hP hPm hR n⟩, ?_⟩
  · intro S h hh
    rcases learner_support H d Aw ε δ S h hh with hU | hc
    · exact hPm.1 h hU
    · subst hc
      exact (measurableSet_singleton true).preimage measurable_snd
        |>.congr (by ext z; cases z.2 <;> simp_all)
  obtain ⟨hstar, hstarH, hstar_ae⟩ := hR
  have hstarU : hstar ∈ PrivLittlestone.localUniverse H d := by
    intro A _
    exact ⟨hstar, hstarH, fun _ _ => rfl⟩
  have hvc' := hvc X (PrivLittlestone.localUniverse H d) d hd1
    (vcDim_localUniverse_le H d hH hd hd1) α (β / 2) hα hα1 (by positivity) (by linarith)
    P hP hPm n hvcn
  have hlow := lower_bound (littlestoneLearner H d Aw ε δ) P (PrivLittlestone.localUniverse H d)
    hPm hstar hstarU hstar_ae α (β / 2) (β / 2) n hvc' (by
      intro s hs
      have hlen : (List.ofFn s).length = n := List.length_ofFn
      have hu := learner_utility H d hH hd hd1 Aw hAw ε δ hε hε1 hδ hδ1 (List.ofFn s) hstar hstarH
        (by
          intro z hz
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
          exact hs i)
        (by rw [hlen]; exact hdn) (β / 2) (by positivity) (by linarith)
      refine hu.trans (MeasureTheory.OuterMeasure.mono _ ?_)
      intro h ⟨hU, hle⟩
      refine ⟨hU, ?_⟩
      unfold empiricalRate
      rw [hlen, div_le_iff₀ (by exact_mod_cast hnpos)]
      rw [hlen] at hle
      linarith)
  refine le_trans ?_ hlow
  rw [← ENNReal.ofReal_mul (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

end MoranYanPAC.Dev.Goal
end

section
set_option autoImplicit false
open MeasureTheory
open MoranYanPAC
open MoranYanPAC.Dev
open MoranYanPAC.Dev.Goal
open MoranYanPAC.Main MoranYanPAC.Learner
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [MeasurableSpace X]
      (H : Set (X → Bool)) (d : ℕ), H.Nonempty →
      UnderstandingML.ldim H = d → 1 ≤ d →
      ∀ (α β ε δ : ℝ), 0 < α → α < 1 → 0 < β → β < 1 →
        0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
      ∃ A : List (X × Bool) → PMF (X → Bool), Private A ε δ ∧
        ∀ P : Measure (X × Bool), IsProbabilityMeasure P →
          VCEventsMeasurable (PrivLittlestone.localUniverse H d) P → Realizable H P →
          ∀ n : ℕ,
            ⌈C * ((d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) +
              Real.log (1 / β)) / (α * ε)⌉₊ ≤ n →
            PACExperimentMeasurable A P α n ∧
            ENNReal.ofReal (1 - β) ≤ pacSuccessProbability A P α n := by
  exact MoranYanPAC.Dev.Goal.private_pac_nearly_linear_dev
end
