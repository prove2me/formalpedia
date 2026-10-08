-- Prove2me | solution 1 for MondererShapley.Improvement.exists_represent
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:22:51.619997+00:00
-- url     : https://prove2.me/submissions/e577c266-d42c-48ee-a559-bdbd5cd6f5f6

import Mathlib
import Definitions.Def_MondererShapley_Improvement_ImprovesTo
import Definitions.Def_MondererShapley_Improvement_HasFIP

open MondererShapley.Improvement Relation

namespace Round35

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

def gain (u : ι → (∀ i, Y i) → ℝ) (a b : ∀ i, Y i) : Prop :=
  ∃ i, MondererShapley.ClosedPath.IsStep b a i ∧ u i b < u i a

lemma gain_wf (u : ι → (∀ i, Y i) → ℝ) (hf : HasFIP u) : WellFounded (gain u) := by
  classical
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨?_⟩
  rintro ⟨y, hy⟩
  choose d hd using hy
  exact hf ⟨y, d, hd⟩

lemma path_reach (u : ι → (∀ i, Y i) → ℝ) (γ : FinPath Y)
    (hγ : γ.IsImprovement u) :
    ReflTransGen (gain u) (γ.pt (Fin.last γ.len)) (γ.pt 0) := by
  have haux : ∀ k : ℕ, (hk : k ≤ γ.len) →
      ReflTransGen (gain u) (γ.pt ⟨k,hk.trans_lt (Nat.lt_succ_self _)⟩) (γ.pt 0) := by
    intro k
    induction k with
    | zero => intro hk; exact ReflTransGen.refl
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hstep : gain u (γ.pt ⟨k+1, by omega⟩) (γ.pt ⟨k, by omega⟩) :=
        ⟨γ.dev ⟨k, by omega⟩, γ.step ⟨k, by omega⟩, hγ ⟨k, by omega⟩⟩
      exact hi.head hstep
  exact haux γ.len le_rfl

lemma represent [Fintype ι] [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (hFIP : HasFIP u) :
    ∃ Q : (∀ i, Y i) → ℝ, ∀ x y, ImprovesTo u x y → Q y < Q x := by
  classical
  let D := fun x : ∀ i, Y i => Finset.univ.filter (fun z => TransGen (gain u) z x)
  refine ⟨fun x => -(D x).card, ?_⟩
  intro x y hxy
  obtain ⟨hne, γ, hγ, hy, hx⟩ := hxy
  have hr : TransGen (gain u) x y := by
    have ht := path_reach u γ hγ
    rw [hx, hy] at ht
    rcases reflTransGen_iff_eq_or_transGen.mp ht with he | ht
    · exact (hne he.symm).elim
    · exact ht
  have hw := (gain_wf u hFIP).transGen
  have hss : D x ⊂ D y := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro z hz
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.trans hr
    · intro he
      have hm : x ∈ D y := by simp [D, hr]
      rw [← he] at hm
      have ht : TransGen (gain u) x x := by simpa [D] using hm
      exact hw.asymmetric x x ht ht
  have hc := Finset.card_lt_card hss
  exact neg_lt_neg (by exact_mod_cast hc)

end Round35

theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*}
    [Fintype ι] [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (hFIP : HasFIP u) :
    ∃ Q : (∀ i, Y i) → ℝ,
      ∀ x y, ImprovesTo u x y → Q y < Q x := by
  exact Round35.represent u hFIP

#print axioms solution
