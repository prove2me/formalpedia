-- Prove2me | solution 1 for MetricTSPSublinear.cutLP_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:39:48.986388+00:00
-- url     : https://prove2.me/submissions/7b117e4e-bfd4-476e-a86f-f4910f49c9cc

import Mathlib
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_IsDualFeasible
import Definitions.Def_DoublingMST_IsMetric
import Theorems.Thm_Polyhedral_lp_strong_duality

open scoped Classical
open MetricTSPSublinear

namespace MTSPDual

/-- LP strong duality for standard-form LPs indexed by arbitrary finite types. -/
theorem lp_sd {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℝ) (c : κ → ℝ) (g : ι → ℝ)
    (u0 : κ → ℝ) (hu0 : ∀ j, 0 ≤ u0 j) (hM : ∀ i, ∑ j, M i j * u0 j = g i)
    (hopt : ∀ u : κ → ℝ, (∀ j, 0 ≤ u j) → (∀ i, ∑ j, M i j * u j = g i) →
      ∑ j, c j * u0 j ≤ ∑ j, c j * u j) :
    ∃ p : ι → ℝ, (∀ j, ∑ i, M i j * p i ≤ c j) ∧ ∑ i, g i * p i = ∑ j, c j * u0 j := by
  set eι := Fintype.equivFin ι
  set eκ := Fintype.equivFin κ
  obtain ⟨p, hp1, hp2, -⟩ := Polyhedral.lp_strong_duality
    (Matrix.of fun a b => M (eι.symm a) (eκ.symm b)) (c ∘ eκ.symm) (g ∘ eι.symm) (u0 ∘ eκ.symm)
    (fun j => hu0 _) (by
      funext a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp]
      rw [Equiv.sum_comp eκ.symm (fun j => M (eι.symm a) j * u0 j)]
      exact hM _) (by
      intro u hu hMu
      have := hopt (u ∘ eκ) (fun j => hu _) (by
        intro i
        have h := congrFun hMu (eι i)
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp,
          Equiv.symm_apply_apply] at h
        rw [← h, ← Equiv.sum_comp eκ.symm]
        simp)
      simp only [dotProduct, Function.comp]
      rw [Equiv.sum_comp eκ.symm (fun j => c j * u0 j)]
      rw [← Equiv.sum_comp eκ.symm (fun j => c j * (u ∘ eκ) j)] at this
      simpa using this)
  refine ⟨p ∘ eι, fun j => ?_, ?_⟩
  · have h := hp1 (eκ j)
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Function.comp,
      Equiv.symm_apply_apply] at h
    rw [← Equiv.sum_comp eι.symm]
    simpa using h
  · simp only [dotProduct, Function.comp] at hp2
    rw [Equiv.sum_comp eκ.symm (fun j => c j * u0 j)] at hp2
    rw [← hp2, ← Equiv.sum_comp eι.symm]
    simp

variable {n : ℕ}

/-- `A` is a cut of `S`: `∅ ≠ A ⊊ S`. -/
abbrev IsCut (S A : Finset (Fin n)) : Prop := A ⊆ S ∧ A.Nonempty ∧ A ≠ S

/-- The primal objective. -/
noncomputable def obj (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (x : Sym2 (Fin n) → ℝ) : ℝ :=
  ∑ e ∈ pairsIn S, DoublingMST.edgeCost d e * x e

lemma mem_pairsIn {S : Finset (Fin n)} {u v : Fin n} :
    s(u, v) ∈ pairsIn S ↔ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  simp [pairsIn, Sym2.mk_isDiag_iff, and_assoc]

lemma mem_cutEdges {S A : Finset (Fin n)} (_hA : A ⊆ S) {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) :
    s(u, v) ∈ cutEdges S A ↔ ¬ (u ∈ A ↔ v ∈ A) := by
  simp only [cutEdges, Finset.mem_image, Finset.mem_product, Finset.mem_sdiff, Prod.exists,
    Sym2.eq_iff]
  constructor
  · rintro ⟨a, b, ⟨ha, -, hb⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> tauto
  · intro h
    by_cases huA : u ∈ A
    · exact ⟨u, v, ⟨huA, hv, by tauto⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, u, ⟨by tauto, hu, huA⟩, Or.inr ⟨rfl, rfl⟩⟩

lemma cutEdges_subset {S A : Finset (Fin n)} (hA : A ⊆ S) : cutEdges S A ⊆ pairsIn S := by
  intro e he
  simp only [cutEdges, Finset.mem_image, Finset.mem_product, Finset.mem_sdiff, Prod.exists] at he
  obtain ⟨a, b, ⟨ha, hb, hbA⟩, rfl⟩ := he
  rw [mem_pairsIn]
  exact ⟨hA ha, hb, fun h => hbA (h ▸ ha)⟩

lemma edgeCost_mk {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (u v : Fin n) :
    DoublingMST.edgeCost d s(u, v) = d u v := by
  simp [DoublingMST.edgeCost, hd.2.1 v u]

lemma metric_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (u v : Fin n) :
    0 ≤ d u v := by
  have h := hd.2.2 u v u
  rw [(hd.1 u u).2 rfl, hd.2.1 v u] at h
  linarith

lemma edgeCost_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (e : Sym2 (Fin n)) :
    0 ≤ DoublingMST.edgeCost d e := by
  induction e using Sym2.ind with
  | h u v => rw [edgeCost_mk hd]; exact metric_nonneg hd u v

lemma edgeCost_pos {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) {S : Finset (Fin n)}
    {e : Sym2 (Fin n)} (he : e ∈ pairsIn S) : 0 < DoublingMST.edgeCost d e := by
  induction e using Sym2.ind with
  | h u v =>
    rw [mem_pairsIn] at he
    rw [edgeCost_mk hd]
    exact lt_of_le_of_ne (metric_nonneg hd u v) (fun h => he.2.2 ((hd.1 u v).1 h.symm))

lemma sum_cut_eq {S : Finset (Fin n)} {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S)
    (f : Finset (Fin n) → ℝ) (hf : ∀ A, ¬ IsCut S A → f A = 0) :
    ∑ A, (if IsCut S A ∧ s(u, v) ∈ cutEdges S A then f A else 0) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))), f A := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases hc : IsCut S A
  · simp only [mem_cutEdges hc.1 hu hv]; exact if_congr (and_iff_right hc) rfl rfl
  · simp [hc, hf A hc]

lemma weak {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (y : Finset (Fin n) → ℝ) (hy : IsDualFeasible d S y) (x : Sym2 (Fin n) → ℝ)
    (hx : IsCutFeasible S x) : ∑ A, y A ≤ obj d S x := by
  obtain ⟨hy0, hyc, hyd⟩ := hy
  obtain ⟨hx0, hxc⟩ := hx
  have hdual : ∀ e ∈ pairsIn S, ∑ A, (if IsCut S A ∧ e ∈ cutEdges S A then y A else 0) ≤
      DoublingMST.edgeCost d e := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [mem_pairsIn] at he
      rw [sum_cut_eq he.1 he.2.1 y hyc, edgeCost_mk hd]
      exact hyd u he.1 v he.2.1 he.2.2
  calc ∑ A, y A = ∑ A, (if IsCut S A then y A else 0) := Finset.sum_congr rfl fun A _ => by
          split_ifs with h
          · rfl
          · exact hyc A h
    _ ≤ ∑ A, (if IsCut S A then y A * ∑ e ∈ cutEdges S A, x e else 0) :=
          Finset.sum_le_sum fun A _ => by
          split_ifs with h
          · exact le_mul_of_one_le_right (hy0 A) (hxc A h.1 h.2.1 h.2.2)
          · exact le_rfl
    _ = ∑ A, ∑ e ∈ pairsIn S, (if IsCut S A ∧ e ∈ cutEdges S A then y A else 0) * x e :=
          Finset.sum_congr rfl fun A _ => by
          split_ifs with h
          · rw [Finset.mul_sum, ← Finset.sum_subset (cutEdges_subset h.1)
              (f := fun e => (if IsCut S A ∧ e ∈ cutEdges S A then y A else 0) * x e)]
            · exact Finset.sum_congr rfl fun e he => by simp [h, he]
            · intro e _ he; simp [he]
          · simp [h]
    _ = ∑ e ∈ pairsIn S, x e * ∑ A, (if IsCut S A ∧ e ∈ cutEdges S A then y A else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun A _ => mul_comm _ _
    _ ≤ obj d S x := by
          unfold obj
          refine Finset.sum_le_sum fun e he => ?_
          rw [mul_comm (DoublingMST.edgeCost d e)]
          exact mul_le_mul_of_nonneg_left (hdual e he) (hx0 e)

lemma one_feasible (S : Finset (Fin n)) : IsCutFeasible S (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun A hA hne hAS => ?_⟩
  have hS : (S \ A).Nonempty := Finset.sdiff_nonempty.mpr (fun h => hAS (subset_antisymm hA h))
  have : (cutEdges S A).Nonempty := ((hne.product hS).image _)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.one_le_cast]
  exact Finset.card_pos.mpr this

lemma restrict_feasible {S : Finset (Fin n)} {x : Sym2 (Fin n) → ℝ} (hx : IsCutFeasible S x) :
    IsCutFeasible S (fun e => if e ∈ pairsIn S then x e else 0) := by
  refine ⟨fun e => ?_, fun A hA hne hAS => ?_⟩
  · dsimp only
    split_ifs
    · exact hx.1 e
    · exact le_rfl
  · rw [Finset.sum_congr rfl fun e he => if_pos (cutEdges_subset hA he)]
    exact hx.2 A hA hne hAS

lemma obj_restrict (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (x : Sym2 (Fin n) → ℝ) :
    obj d S (fun e => if e ∈ pairsIn S then x e else 0) = obj d S x := by
  unfold obj
  exact Finset.sum_congr rfl fun e he => by dsimp only; rw [if_pos he]

lemma exists_opt {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) :
    ∃ x, IsCutFeasible S x ∧ ∀ x', IsCutFeasible S x' → obj d S x ≤ obj d S x' := by
  set P := pairsIn S with hP
  set B := obj d S (fun _ => 1) with hB
  let b : Sym2 (Fin n) → ℝ := fun e => if e ∈ P then B / DoublingMST.edgeCost d e else 0
  let K : Set (Sym2 (Fin n) → ℝ) :=
    {x | IsCutFeasible S x ∧ obj d S x ≤ B ∧ ∀ e, e ∉ P → x e = 0}
  have hcont : Continuous (obj d S) := by unfold obj; fun_prop
  have hKc : IsClosed K := by
    have h1 : IsClosed {x : Sym2 (Fin n) → ℝ | ∀ e, 0 ≤ x e} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)
    have h2 : IsClosed {x : Sym2 (Fin n) → ℝ |
        ∀ A ⊆ S, A.Nonempty → A ≠ S → 1 ≤ ∑ e ∈ cutEdges S A, x e} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun A => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)
    have h3 : IsClosed {x | obj d S x ≤ B} := isClosed_le hcont continuous_const
    have h4 : IsClosed {x : Sym2 (Fin n) → ℝ | ∀ e, e ∉ P → x e = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun e => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply e) continuous_const
    have : K = ({x : Sym2 (Fin n) → ℝ | ∀ e, 0 ≤ x e} ∩ {x : Sym2 (Fin n) → ℝ |
        ∀ A ⊆ S, A.Nonempty → A ≠ S → 1 ≤ ∑ e ∈ cutEdges S A, x e}) ∩
        ({x | obj d S x ≤ B} ∩ {x : Sym2 (Fin n) → ℝ | ∀ e, e ∉ P → x e = 0}) := by
      ext x; simp only [K, IsCutFeasible, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact (h1.inter h2).inter (h3.inter h4)
  have hsub : K ⊆ Set.pi Set.univ (fun e => Set.Icc 0 (b e)) := by
    intro x hx e _
    obtain ⟨⟨hx0, -⟩, hxB, hxP⟩ := hx
    refine ⟨hx0 e, ?_⟩
    simp only [b]
    split_ifs with he
    · rw [le_div_iff₀ (edgeCost_pos hd he), mul_comm]
      refine le_trans ?_ hxB
      exact Finset.single_le_sum (f := fun e => DoublingMST.edgeCost d e * x e)
        (fun e _ => mul_nonneg (edgeCost_nonneg hd e) (hx0 e)) he
    · exact (hxP e he).le
  have hKcomp : IsCompact K :=
    (isCompact_univ_pi fun e => isCompact_Icc).of_isClosed_subset hKc hsub
  have h1K : (fun e => if e ∈ P then (1 : ℝ) else 0) ∈ K := by
    refine ⟨restrict_feasible (one_feasible S), ?_, fun e he => if_neg he⟩
    rw [obj_restrict]
  obtain ⟨xs, hxsK, hmin⟩ := hKcomp.exists_isMinOn ⟨_, h1K⟩ hcont.continuousOn
  refine ⟨xs, hxsK.1, fun x' hx' => ?_⟩
  by_cases hle : obj d S x' ≤ B
  · have hmem : (fun e => if e ∈ P then x' e else 0) ∈ K := by
      refine ⟨restrict_feasible hx', ?_, fun e he => if_neg he⟩
      rw [obj_restrict]; exact hle
    have := isMinOn_iff.mp hmin _ hmem
    rwa [obj_restrict] at this
  · have := isMinOn_iff.mp hmin _ h1K
    rw [obj_restrict] at this
    linarith

lemma cutLP_eq_of_opt {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (x : Sym2 (Fin n) → ℝ) (hx : IsCutFeasible S x)
    (hopt : ∀ x', IsCutFeasible S x' → obj d S x ≤ obj d S x') : cutLP d S = obj d S x := by
  have hbdd : BddBelow {t : ℝ | ∃ x : Sym2 (Fin n) → ℝ, IsCutFeasible S x ∧
      t = ∑ e ∈ pairsIn S, DoublingMST.edgeCost d e * x e} :=
    ⟨0, by
      rintro t ⟨x, hx, rfl⟩
      exact Finset.sum_nonneg fun e _ => mul_nonneg (edgeCost_nonneg hd e) (hx.1 e)⟩
  apply le_antisymm
  · exact csInf_le hbdd ⟨x, hx, rfl⟩
  · refine le_csInf ⟨obj d S x, x, hx, rfl⟩ ?_
    rintro t ⟨x', hx', rfl⟩
    exact hopt x' hx'

theorem cutLP_attained {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) :
    ∃ x : Sym2 (Fin n) → ℝ, IsCutFeasible S x ∧
      ∑ e ∈ pairsIn S, DoublingMST.edgeCost d e * x e = cutLP d S := by
  obtain ⟨x, hx, hopt⟩ := exists_opt hd S
  exact ⟨x, hx, (cutLP_eq_of_opt hd S x hx hopt).symm⟩

theorem weak_duality {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ) (hy : MetricTSPSublinear.IsDualFeasible d S y) :
    ∑ A, y A ≤ MetricTSPSublinear.cutLP d S := by
  obtain ⟨x, hx, hopt⟩ := exists_opt hd S
  rw [cutLP_eq_of_opt hd S x hx hopt]
  exact weak hd S y hy x hx

theorem strong_duality {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) :
    ∃ y : Finset (Fin n) → ℝ, MetricTSPSublinear.IsDualFeasible d S y ∧
      ∑ A, y A = MetricTSPSublinear.cutLP d S := by
  obtain ⟨xs, hxs, hopt⟩ := exists_opt hd S
  rw [cutLP_eq_of_opt hd S xs hxs hopt]
  let M : Finset (Fin n) → Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ := fun A j =>
    Sum.elim (fun e => if IsCut S A ∧ e ∈ cutEdges S A then 1 else 0)
      (fun B => if A = B then (if IsCut S A then -1 else 0) else 0) j
  let c : Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ :=
    Sum.elim (fun e => if e ∈ pairsIn S then DoublingMST.edgeCost d e else 0) (fun _ => 0)
  let g : Finset (Fin n) → ℝ := fun A => if IsCut S A then 1 else 0
  have hMsum : ∀ A (v : Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ), ∑ j, M A j * v j =
      if IsCut S A then ∑ e ∈ cutEdges S A, v (Sum.inl e) - v (Sum.inr A) else 0 := by
    intro A v
    rw [Fintype.sum_sum_type]
    split_ifs with h
    · simp [M, sub_eq_add_neg, ite_mul]
      rw [if_pos h]
      simp only [and_iff_right h]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    · simp [M, h]
  have hcsum : ∀ v : Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ,
      ∑ j, c j * v j = obj d S (fun e => v (Sum.inl e)) := by
    intro v
    rw [Fintype.sum_sum_type]
    simp [c, obj, ite_mul]
  let u0 : Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ :=
    Sum.elim xs (fun A => if IsCut S A then ∑ e ∈ cutEdges S A, xs e - 1 else 0)
  obtain ⟨p, hp, hpv⟩ := lp_sd M c g u0
    (by
      rintro (e | A)
      · exact hxs.1 e
      · simp only [u0, Sum.elim_inr]
        split_ifs with h
        · linarith [hxs.2 A h.1 h.2.1 h.2.2]
        · exact le_rfl)
    (by
      intro A
      rw [hMsum]
      simp only [u0, Sum.elim_inl, Sum.elim_inr, g]
      split_ifs <;> ring)
    (by
      intro u hu hMu
      rw [hcsum, hcsum]
      refine hopt _ ⟨fun e => hu _, fun A hA hne hAS => ?_⟩
      have h := hMu A
      rw [hMsum] at h
      simp only [g, if_pos (show IsCut S A from ⟨hA, hne, hAS⟩)] at h
      linarith [hu (Sum.inr A)])
  let y : Finset (Fin n) → ℝ := fun A => if IsCut S A then p A else 0
  refine ⟨y, ⟨fun A => ?_, fun A hA => ?_, fun u hu v hv huv => ?_⟩, ?_⟩
  · simp only [y]
    split_ifs with h
    · have := hp (Sum.inr A)
      simp [M, c] at this
      rw [if_pos h] at this
      linarith
    · exact le_rfl
  · simp only [y]
    exact if_neg hA
  · rw [← sum_cut_eq hu hv y (fun A h => by simp only [y]; exact if_neg h)]
    have := hp (Sum.inl s(u, v))
    simp only [M, c, Sum.elim_inl, if_pos (mem_pairsIn.mpr ⟨hu, hv, huv⟩), edgeCost_mk hd]
      at this
    refine le_of_eq_of_le (Finset.sum_congr rfl fun A _ => ?_) this
    by_cases h : IsCut S A ∧ s(u, v) ∈ cutEdges S A
    · simp [y, h.1, h]
    · simp [h]
  · rw [show ∑ A, y A = ∑ A, g A * p A from
      Finset.sum_congr rfl fun A _ => by simp only [y, g]; split_ifs <;> ring, hpv, hcsum]
    rfl

end MTSPDual

open MetricTSPSublinear in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) :
    ∃ y : Finset (Fin n) → ℝ, IsDualFeasible d S y ∧ ∑ A, y A = cutLP d S :=
  MTSPDual.strong_duality d hd S
