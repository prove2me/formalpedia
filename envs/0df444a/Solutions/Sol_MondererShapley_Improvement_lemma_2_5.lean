-- Prove2me | solution 1 for MondererShapley.Improvement.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:22:52.896521+00:00
-- url     : https://prove2.me/submissions/a2e3f173-5e20-41fa-8f04-dd20e5ec8bfb

import Mathlib
import Definitions.Def_MondererShapley_Improvement_ImprovesTo
import Definitions.Def_MondererShapley_Improvement_HasFIP
import Definitions.Def_MondererShapley_Improvement_IsGenOrdinalPotential

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

open MondererShapley.Improvement

theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*}
    [Fintype ι] [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) :
    HasFIP u ↔ ∃ P : (∀ i, Y i) → ℝ, IsGenOrdinalPotential u P := by
  classical
  constructor
  · intro hf
    obtain ⟨Q, hQ⟩ := Round35.represent u hf
    refine ⟨Q, ?_⟩
    intro i y x z hgain
    have hxz : x ≠ z := by
      intro he; subst z; simp at hgain
    let a := Function.update y i z
    let b := Function.update y i x
    have hstep : MondererShapley.ClosedPath.IsStep a b i := by
      refine ⟨by simpa [a,b] using hxz, ?_⟩
      intro j hj
      simp [a,b,Function.update_of_ne hj]
    let γ : FinPath Y :=
      { len := 1
        pt := fun k => if k.val = 0 then a else b
        dev := fun _ => i
        step := by intro k; have hk : k = 0 := Fin.eq_zero k; subst k; simpa using hstep }
    have hab : b ≠ a := by
      intro he
      have he' := congrFun he i
      exact hxz (by simpa [a,b] using he')
    have hreach : ImprovesTo u b a := by
      refine ⟨hab, γ, ?_, ?_, ?_⟩
      · intro k
        have hk : k = 0 := Fin.eq_zero k
        subst k
        simpa [γ,a,b,sub_pos] using hgain
      · simp [γ]
      · simp [γ]
    exact sub_pos.mpr (hQ b a hreach)
  · rintro ⟨P, hP⟩ ⟨y,d,hd⟩
    have hup (k : ℕ) : Function.update (y k) (d k) (y (k+1) (d k)) = y (k+1) := by
      funext j
      by_cases hj : j = d k
      · subst j; simp
      · simpa [Function.update_of_ne hj] using (hd k).1.2 j hj |>.symm
    have hmono : StrictMono (fun k => P (y k)) := by
      apply strictMono_nat_of_lt_succ
      intro k
      have ht := hP (d k) (y k) (y (k+1) (d k)) (y k (d k))
        (by simpa only [hup k, Function.update_eq_self, sub_pos] using (hd k).2)
      simpa only [hup k, Function.update_eq_self, sub_pos] using ht
    have hinj : Function.Injective y := fun a b hab => hmono.injective (congrArg P hab)
    letI := Finite.of_injective y hinj
    exact not_finite ℕ

#print axioms solution
