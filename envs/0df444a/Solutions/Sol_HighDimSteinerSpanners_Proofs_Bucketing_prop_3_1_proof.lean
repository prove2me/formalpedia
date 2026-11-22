-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Bucketing.prop_3_1_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:29.049619+00:00
-- url     : https://prove2.me/submissions/9428753c-3fdd-436a-a132-a0932a187146

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Bucketing
section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Bucketing
private lemma bucketDiam_nonneg {P : Type} [MetricSpace P] (s : Finset P) :
    0 ≤ bucketDiam s := by
  unfold bucketDiam
  by_cases hne : s.Nonempty
  · rw [dif_pos hne]
    have ⟨u, hu⟩ := hne
    have h1 : (0 : ℝ) ≤ s.sup' hne (fun v => dist u v) := by
      have := Finset.le_sup' (f := fun v => dist u v) hu
      simpa only [dist_self] using this
    exact h1.trans (Finset.le_sup' (f := fun u' => s.sup' hne (fun v => dist u' v)) hu)
  · rw [dif_neg hne]
private lemma dist_le_bucketDiam {P : Type} [MetricSpace P] {s : Finset P} {u v : P}
    (hu : u ∈ s) (hv : v ∈ s) : dist u v ≤ bucketDiam s := by
  have hne : s.Nonempty := ⟨u, hu⟩
  unfold bucketDiam
  rw [dif_pos hne]
  have h1 : dist u v ≤ s.sup' hne (fun v' => dist u v') :=
    Finset.le_sup' (f := fun v' => dist u v') hv
  exact h1.trans (Finset.le_sup' (f := fun u' => s.sup' hne (fun v' => dist u' v')) hu)
private lemma bucketingWalkInv_holds {P I : Type} [MetricSpace P] (B : I → Finset P)
    {u v : P ⊕ I} (q : (bucketingGraph B).Walk u v) : bucketingWalkInv B u v q := by
  induction q with
  | nil =>
    rename_i u
    cases u with
    | inl x => simp [bucketingWalkInv, walkWeight]
    | inr i => trivial
  | @cons u b v hadj q' ih =>
    cases v with
    | inr j => cases u <;> trivial
    | inl y =>
      cases u with
      | inl x =>
        cases b with
        | inl z => exact False.elim hadj
        | inr i =>
          have hx : x ∈ B i := hadj
          have hstep := ih x hx
          simpa [bucketingWalkInv, walkWeight, bucketingWeight] using hstep
      | inr i =>
        cases b with
        | inr j => exact False.elim hadj
        | inl z =>
          have hz : z ∈ B i := hadj
          dsimp [bucketingWalkInv] at ih ⊢
          intro x hx
          have hxz : dist x z ≤ bucketDiam (B i) := dist_le_bucketDiam hx hz
          have htri : dist x y ≤ dist x z + dist z y := dist_triangle x z y
          have hw_eq : bucketingWeight B s(Sum.inr i, Sum.inl z) = bucketDiam (B i) / 2 := rfl
          simp only [walkWeight, hw_eq]
          linarith
end HighDimSteinerSpanners.Proofs.Bucketing
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Bucketing
namespace HighDimSteinerSpanners.Proofs.Bucketing
theorem _root_.solution :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C : ℝ), 1 ≤ C →
        ∀ (I : Type) [Fintype I] (B : I → Finset P),
          (∀ i : I, 2 ≤ (B i).card) →
          (Nat.card (bucketingGraph B).edgeSet = ∑ i : I, (B i).card ∧
            ∀ x y : P,
              ENNReal.ofReal (dist x y) ≤
                graphDist (bucketingGraph B) (bucketingWeight B) (.inl x) (.inl y)) ∧
          ((∀ x y : P, x ≠ y → ∃ i : I, x ∈ B i ∧ y ∈ B i ∧ bucketDiam (B i) ≤ C * dist x y) →
            IsGeneralNonMetricSteinerSpanner C (bucketingGraph B) (bucketingWeight B) ∧
            ∀ x y : P, x ≠ y →
              ∃ q : (bucketingGraph B).Walk (.inl x) (.inl y),
                q.IsPath ∧ q.length ≤ 2 ∧
                walkWeight (bucketingWeight B) q ≤ C * dist x y) := by
  intro P _ _ _hP C _hC I _ B _hB
  have hcard : Nat.card (bucketingGraph B).edgeSet = ∑ i : I, (B i).card := by
    let f : (Σ i : I, ↥(B i)) → (bucketingGraph B).edgeSet := fun ⟨i, ⟨x, hx⟩⟩ =>
      ⟨s(.inl x, .inr i), (bucketingGraph B).mem_edgeSet.mpr hx⟩
    have hf_bij : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · rintro ⟨i₁, ⟨x₁, hx₁⟩⟩ ⟨i₂, ⟨x₂, hx₂⟩⟩ heq
        have hs : (s(Sum.inl x₁, Sum.inr i₁) : Sym2 (P ⊕ I)) = s(Sum.inl x₂, Sum.inr i₂) :=
          congrArg Subtype.val heq
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨h1, h2⟩ | ⟨h1, _⟩
        · injection h1 with hx_eq
          injection h2 with hi_eq
          subst hi_eq hx_eq
          rfl
        · exact False.elim (Sum.inl_ne_inr h1)
      · rintro ⟨e, he⟩
        revert he
        refine Sym2.ind (fun u v he => ?_) e
        rw [SimpleGraph.mem_edgeSet] at he
        cases u with
        | inl x =>
          cases v with
          | inl y => exact False.elim he
          | inr i => exact ⟨⟨i, ⟨x, he⟩⟩, rfl⟩
        | inr i =>
          cases v with
          | inl x =>
            refine ⟨⟨i, ⟨x, he⟩⟩, Subtype.ext ?_⟩
            exact Sym2.eq_swap
          | inr j => exact False.elim he
    rw [← Nat.card_congr (Equiv.ofBijective f hf_bij)]
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
  have hnoncontract : ∀ x y : P,
      ENNReal.ofReal (dist x y) ≤
        graphDist (bucketingGraph B) (bucketingWeight B) (.inl x) (.inl y) := by
    intro x y
    refine le_iInf (fun q => ?_)
    exact ENNReal.ofReal_le_ofReal (bucketingWalkInv_holds B q)
  refine ⟨⟨hcard, hnoncontract⟩, ?_⟩
  intro hcov
  have h2hop : ∀ x y : P, x ≠ y →
      ∃ q : (bucketingGraph B).Walk (.inl x) (.inl y),
        q.IsPath ∧ q.length ≤ 2 ∧
        walkWeight (bucketingWeight B) q ≤ C * dist x y := by
    intro x y hxy
    obtain ⟨i, hx, hy, hdiam⟩ := hcov x y hxy
    have hadj1 : (bucketingGraph B).Adj (.inl x) (.inr i) := hx
    have hadj2 : (bucketingGraph B).Adj (.inr i) (.inl y) := hy
    let q : (bucketingGraph B).Walk (.inl x) (.inl y) := .cons hadj1 (.cons hadj2 .nil)
    refine ⟨q, ?_, by simp [q], ?_⟩
    · rw [SimpleGraph.Walk.isPath_def]
      simp [q, hxy]
    · have hw1 : bucketingWeight B s(Sum.inl x, Sum.inr i) = bucketDiam (B i) / 2 := rfl
      have hw2 : bucketingWeight B s(Sum.inr i, Sum.inl y) = bucketDiam (B i) / 2 := rfl
      simp only [q, walkWeight, hw1, hw2]
      linarith
  refine ⟨?_, h2hop⟩
  refine ⟨?_, hnoncontract, ?_⟩
  · intro e _he
    refine Sym2.ind (fun u v => ?_) e
    cases u <;> cases v <;> simp only [bucketingWeight, Sym2.lift_mk, Std.le_refl]
    · exact div_nonneg (bucketDiam_nonneg _) (by norm_num)
    · exact div_nonneg (bucketDiam_nonneg _) (by norm_num)
  · intro x y
    by_cases hxy : x = y
    · subst hxy
      calc
        graphDist (bucketingGraph B) (bucketingWeight B) (.inl x) (.inl x)
          ≤ ENNReal.ofReal (walkWeight (bucketingWeight B) SimpleGraph.Walk.nil) :=
            iInf_le _ SimpleGraph.Walk.nil
        _ = 0 := by simp [walkWeight]
        _ ≤ ENNReal.ofReal (C * dist x x) := zero_le
    · obtain ⟨q, _, _, hqw⟩ := h2hop x y hxy
      exact (iInf_le _ q).trans (ENNReal.ofReal_le_ofReal hqw)
end HighDimSteinerSpanners.Proofs.Bucketing
