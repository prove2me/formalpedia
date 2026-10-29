-- Prove2me | solution 1 for MatroidProphetKW.Inter.intersection_prophet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T02:58:21.710142+00:00
-- url     : https://prove2.me/submissions/40d01a5e-e1ba-481f-916a-719751c53720

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online
import Theorems.Thm_MatroidProphetKW_Inter_proposition_3
import Theorems.Thm_MatroidProphetKW_Inter_eq_13
import Theorems.Thm_MatroidProphetKW_Inter_eq_14

/-!
Kleinberg & Weinberg, arXiv:1201.4764v1, §4.2: the summed-threshold algorithm with `α = 2p`
is `2p`-balanced (Eq. (13) via `eq_13`, Eq. (14) via `eq_14`), its thresholds are non-negative
(proved below: `R_j(A ∪ {x})` weighs at most `R_j(A)` for non-negative ghost weights), so
Proposition 3 (`proposition_3`) gives the factor `(2p − p)/(2p(2p − 1)) = 1/(4p − 2)`.
-/

set_option autoImplicit false

open MeasureTheory

open MatroidProphetKW.Inter in
theorem pv15a_firstOf_mem {α : Type*} [Fintype α] [DecidableEq α]
    {S : Finset (Finset α)} (h : S.Nonempty) : firstOf S ∈ S := by
  unfold firstOf
  rw [dif_pos h]
  obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 (Finset.min'_mem _ (h.image (Fintype.equivFin (Finset α))))
  rw [← hse, Equiv.symm_apply_apply]
  exact hs

open MatroidProphetKW.Inter in
theorem pv15a_firstOf_filter {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α → Prop) {inst : DecidablePred Q} (h : ∃ S, Q S) :
    Q (firstOf (@Finset.filter _ Q inst Finset.univ)) := by
  obtain ⟨S, hS⟩ := h
  have hne : (@Finset.filter _ Q inst Finset.univ).Nonempty :=
    ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩⟩
  exact (Finset.mem_filter.1 (pv15a_firstOf_mem hne)).2

open MatroidProphetKW.Inter in
theorem pv15a_firstOf_filter_empty {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α → Prop) {inst : DecidablePred Q} (h : ¬ ∃ S, Q S) :
    firstOf (@Finset.filter _ Q inst Finset.univ) = ∅ := by
  unfold firstOf
  rw [dif_neg]
  rintro ⟨S, hS⟩
  exact h ⟨S, (Finset.mem_filter.1 hS).2⟩

open MatroidProphetKW.Inter in
theorem pv15a_argmaxOn_spec {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α → Prop) (f : Finset α → ℝ) (h : ∃ S, P S) :
    P (argmaxOn P f) ∧ ∀ T, P T → f T ≤ f (argmaxOn P f) := by
  classical
  obtain ⟨S0, hS0⟩ := h
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) f
    ⟨S0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hS0⟩⟩
  unfold argmaxOn
  apply pv15a_firstOf_filter (fun S => P S ∧ ∀ T, P T → f T ≤ f S)
  exact ⟨S, (Finset.mem_filter.1 hS).2,
    fun T hT => hmax T (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩)⟩

open MatroidProphetKW.Inter in
theorem pv15a_argmaxOn_empty {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α → Prop) (f : Finset α → ℝ) (h : ¬ ∃ S, P S) :
    argmaxOn P f = ∅ := by
  classical
  unfold argmaxOn
  apply pv15a_firstOf_filter_empty
  rintro ⟨S, hS, -⟩
  exact h ⟨S, hS⟩

open MatroidProphetKW.Inter in
/-- For non-negative ghost weights, `w′(R_j(A ∪ {x})) ≤ w′(R_j(A))`. -/
theorem pv15a_Rj_mono {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ) (j : Fin p)
    (A : Finset α) (x : α) (w' : α → ℝ) (hw : ∀ y, 0 ≤ w' y) :
    MatroidProphetKW.Single.wt w' (Rj M j (insert x A) w') ≤
      MatroidProphetKW.Single.wt w' (Rj M j A w') := by
  classical
  have hnn : ∀ S : Finset α, 0 ≤ MatroidProphetKW.Single.wt w' S :=
    fun S => Finset.sum_nonneg (fun y _ => hw y)
  have hsubE : ∀ X : Set α, X ⊆ (M j).E := fun X => by rw [hE j]; exact Set.subset_univ _
  let PA : Finset α → Prop := fun R => R ⊆ B M w' \ A ∧ (M j).Indep (↑(A ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(A ∪ R) : Set α)
  let PX : Finset α → Prop := fun R => R ⊆ B M w' \ insert x A ∧
      (M j).Indep (↑(insert x A ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(insert x A ∪ R) : Set α)
  show MatroidProphetKW.Single.wt w' (argmaxOn PX (MatroidProphetKW.Single.wt w')) ≤
    MatroidProphetKW.Single.wt w' (argmaxOn PA (MatroidProphetKW.Single.wt w'))
  by_cases hX : ∃ R, PX R
  · obtain ⟨⟨hsub, hind, hcl⟩, -⟩ := pv15a_argmaxOn_spec PX (MatroidProphetKW.Single.wt w') hX
    set R' := argmaxOn PX (MatroidProphetKW.Single.wt w') with hR'
    have hsubA : R' ⊆ B M w' \ A :=
      hsub.trans (Finset.sdiff_subset_sdiff (le_refl _) (Finset.subset_insert _ _))
    have hcoeX : (↑(insert x A ∪ R') : Set α) = insert x (↑(A ∪ R') : Set α) := by
      rw [Finset.insert_union, Finset.coe_insert]
    have hSind : (M j).Indep (↑(A ∪ R') : Set α) := by
      apply hind.subset
      rw [hcoeX]; exact Set.subset_insert _ _
    by_cases hB : (↑(B M w') : Set α) ⊆ (M j).closure (↑(A ∪ R') : Set α)
    · have hPA : PA R' := ⟨hsubA, hSind, hB⟩
      exact (pv15a_argmaxOn_spec PA _ ⟨R', hPA⟩).2 R' hPA
    · obtain ⟨b, hbB, hbcl⟩ := Set.not_subset.1 hB
      have hbS : b ∉ (↑(A ∪ R') : Set α) :=
        fun hb => hbcl ((M j).subset_closure _ (hsubE _) hb)
      have hbA : b ∉ A := fun hb => hbS (by simp [hb])
      have hbR : b ∉ R' := fun hb => hbS (by simp [hb])
      have hcoeB : (↑(A ∪ insert b R') : Set α) = insert b (↑(A ∪ R') : Set α) := by
        rw [Finset.union_insert, Finset.coe_insert]
      have hindB : (M j).Indep (insert b (↑(A ∪ R') : Set α)) :=
        (hSind.insert_indep_iff_of_notMem hbS).2 ⟨by rw [hE j]; trivial, hbcl⟩
      have hbx : b ∈ (M j).closure (insert x (↑(A ∪ R') : Set α)) \
          (M j).closure (↑(A ∪ R') : Set α) := ⟨by rw [← hcoeX]; exact hcl hbB, hbcl⟩
      have hxb := (M j).closure_exchange hbx
      have hclB : (↑(B M w') : Set α) ⊆ (M j).closure (insert b (↑(A ∪ R') : Set α)) := by
        refine hcl.trans ?_
        rw [hcoeX]
        apply (M j).closure_subset_closure_of_subset_closure
        rw [Set.insert_subset_iff]
        exact ⟨hxb.1, (Set.subset_insert _ _).trans ((M j).subset_closure _ (hsubE _))⟩
      have hPA : PA (insert b R') := by
        refine ⟨?_, by rw [hcoeB]; exact hindB, by rw [hcoeB]; exact hclB⟩
        rw [Finset.insert_subset_iff]
        exact ⟨Finset.mem_sdiff.2 ⟨Finset.mem_coe.1 hbB, hbA⟩, hsubA⟩
      have h1 := (pv15a_argmaxOn_spec PA (MatroidProphetKW.Single.wt w') ⟨_, hPA⟩).2 _ hPA
      have h2 : MatroidProphetKW.Single.wt w' (insert b R') =
          w' b + MatroidProphetKW.Single.wt w' R' := Finset.sum_insert hbR
      linarith [hw b]
  · rw [pv15a_argmaxOn_empty PX _ hX]
    have : MatroidProphetKW.Single.wt w' ∅ = 0 := Finset.sum_empty
    rw [this]
    exact hnn _

open MatroidProphetKW.Inter in
theorem pv15a_ae_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) :
    ∀ᵐ w' ∂(law F), ∀ y, 0 ≤ w' y := by
  rw [ae_all_iff]
  intro y
  rw [ae_iff]
  have hset : {a : α → ℝ | ¬ 0 ≤ a y} = Function.eval y ⁻¹' Set.Iio 0 := by
    ext a; simp
  rw [hset]
  exact Measure.pi_eval_preimage_null F (hF_nonneg y)

open MatroidProphetKW.Inter in
/-- The §4.2 thresholds are non-negative for `α > 0`. -/
theorem pv15a_Tsum_nonneg {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (a : ℝ) (ha : 0 < a) (A : Finset α) (x : α) :
    0 ≤ Tsum M F a A x := by
  apply Finset.sum_nonneg
  intro j _
  unfold Tij
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [pv15a_ae_nonneg F hF_nonneg] with w' hw'
  exact sub_nonneg.2 (pv15a_Rj_mono M hE j A x w' hw')

open MatroidProphetKW.Inter in
theorem solution
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hp : 0 < p) (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (adv : Adversary α) :
    1 / (4 * (p : ℝ) - 2) * ∫ w, OPT M w ∂(law F) ≤
      ∫ w, MatroidProphetKW.Single.wt w (adaptiveSelected (sumRule M F (2 * p)) M adv w) ∂(law F) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have ha2 : (2 : ℝ) ≤ 2 * (p : ℝ) := by linarith
  have hapos : (0 : ℝ) < 2 * (p : ℝ) := by linarith
  have hthr : ∀ A xs w x, 0 ≤ (sumRule M F (2 * (p : ℝ))).thr A xs w x :=
    fun A _ _ x => pv15a_Tsum_nonneg M hE F hF_nonneg _ hapos A x
  have h13 : Balanced13 M F (2 * (p : ℝ)) (sumRule M F (2 * (p : ℝ))) :=
    fun xs hnd hall w _ =>
      le_of_eq (MatroidProphetKW.Inter.eq_13 M hE F hF_nonneg hF_int _ xs hnd hall w).symm
  have h14 : Balanced14 M F (2 * (p : ℝ)) (sumRule M F (2 * (p : ℝ))) :=
    MatroidProphetKW.Inter.eq_14 M hE F hF_nonneg hF_int _ hapos
  have h3 := MatroidProphetKW.Inter.proposition_3 hp M hE F hF_nonneg hF_int (2 * (p : ℝ)) ha2
    (sumRule M F (2 * (p : ℝ))) hthr ⟨h13, h14⟩ adv
  have hcoef : (2 * (p : ℝ) - p) / (2 * (p : ℝ) * (2 * (p : ℝ) - 1)) = 1 / (4 * (p : ℝ) - 2) := by
    have h1 : (2 * (p : ℝ) - 1) ≠ 0 := by linarith
    have h2 : (4 * (p : ℝ) - 2) ≠ 0 := by linarith
    have h3' : (p : ℝ) ≠ 0 := by linarith
    have h4 : 2 * (p : ℝ) * (2 * (p : ℝ) - 1) ≠ 0 := mul_ne_zero (by linarith) h1
    rw [div_eq_div_iff h4 h2]
    ring
  rw [hcoef] at h3
  exact h3
