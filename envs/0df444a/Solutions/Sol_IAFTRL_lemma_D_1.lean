-- Prove2me | solution 1 for IAFTRL.lemma_D_1
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T16:38:14.509712+00:00
-- url     : https://prove2.me/submissions/b8170058-c37a-4f32-b401-ae0cfb15a20b

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsMin2_3
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Theorems.Thm_IAFTRL_lemma_D_10
import Theorems.Thm_IAFTRL_lemma_J_3_finite

/-! ### Lexicographic minimal selections over a closed graph with compact fibres -/

namespace LexSel

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- stage fibres: `fib 0 x = C_x`, `fib (k+1) x = {y ∈ fib k x | κ_k(x,y) ≤ inf_{fib k x} κ_k(x,·)}` -/
def fib (C : Set (X × Y)) (κ : ℕ → X × Y → ℝ) : ℕ → X → Set Y
  | 0, x => {y | (x, y) ∈ C}
  | k + 1, x => {y | y ∈ fib C κ k x ∧
      κ k (x, y) ≤ sInf ((fun y => κ k (x, y)) '' fib C κ k x)}

/-- stage values -/
noncomputable def mval (C : Set (X × Y)) (κ : ℕ → X × Y → ℝ) (k : ℕ) (x : X) : ℝ :=
  sInf ((fun y => κ k (x, y)) '' fib C κ k x)

variable (C : Set (X × Y)) (κ : ℕ → X × Y → ℝ)

lemma mem_fib (k : ℕ) (x : X) (y : Y) :
    y ∈ fib C κ k x ↔ (x, y) ∈ C ∧ ∀ j < k, κ j (x, y) ≤ mval C κ j x := by
  induction k with
  | zero => simp [fib]
  | succ k ih =>
    show (y ∈ fib C κ k x ∧ κ k (x, y) ≤ mval C κ k x) ↔ _
    rw [ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact h2 j h
      · rw [h]; exact h3
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun j hj => h2 j (by omega)⟩, h2 k (by omega)⟩

variable {C κ}

lemma fib_closed (hC : IsClosed C) (hκ : ∀ k, Continuous (κ k)) (k : ℕ) (x : X) :
    IsClosed (fib C κ k x) := by
  have e : fib C κ k x = {y | (x, y) ∈ C} ∩ ⋂ j ∈ Finset.range k, {y | κ j (x, y) ≤ mval C κ j x} := by
    ext y; rw [mem_fib]; simp
  rw [e]
  refine (hC.preimage (Continuous.prodMk_right x)).inter ?_
  refine isClosed_biInter fun j _ => ?_
  exact isClosed_le ((hκ j).comp (Continuous.prodMk_right x)) continuous_const

lemma fib_sub {Δ : Set Y} (hCΔ : ∀ z ∈ C, z.2 ∈ Δ) (k : ℕ) (x : X) : fib C κ k x ⊆ Δ :=
  fun y hy => hCΔ (x, y) ((mem_fib C κ k x y).mp hy).1

lemma fib_compact (hC : IsClosed C) (hκ : ∀ k, Continuous (κ k)) {Δ : Set Y} (hΔ : IsCompact Δ)
    (hCΔ : ∀ z ∈ C, z.2 ∈ Δ) (k : ℕ) (x : X) : IsCompact (fib C κ k x) :=
  hΔ.of_isClosed_subset (fib_closed hC hκ k x) (fib_sub hCΔ k x)

lemma mval_le (hC : IsClosed C) (hκ : ∀ k, Continuous (κ k)) {Δ : Set Y} (hΔ : IsCompact Δ)
    (hCΔ : ∀ z ∈ C, z.2 ∈ Δ) {k : ℕ} {x : X} {y : Y} (hy : y ∈ fib C κ k x) :
    mval C κ k x ≤ κ k (x, y) := by
  have hc := fib_compact hC hκ hΔ hCΔ k x
  have hb : BddBelow ((fun y => κ k (x, y)) '' fib C κ k x) :=
    (hc.image ((hκ k).comp (Continuous.prodMk_right x))).bddBelow
  exact csInf_le hb ⟨y, hy, rfl⟩

lemma fib_nonempty (hC : IsClosed C) (hκ : ∀ k, Continuous (κ k)) {Δ : Set Y} (hΔ : IsCompact Δ)
    (hCΔ : ∀ z ∈ C, z.2 ∈ Δ) {x : X} (h0 : (fib C κ 0 x).Nonempty) :
    ∀ k, (fib C κ k x).Nonempty := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hc := fib_compact hC hκ hΔ hCΔ k x
    obtain ⟨y0, hy0, hmin⟩ := hc.exists_isMinOn ih
      ((hκ k).comp (Continuous.prodMk_right x)).continuousOn
    refine ⟨y0, hy0, ?_⟩
    have hl : IsLeast ((fun y => κ k (x, y)) '' fib C κ k x) (κ k (x, y0)) :=
      ⟨⟨y0, hy0, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmin hy⟩
    rw [hl.csInf_eq]

lemma proj_closed {D : Set (X × Y)} (hD : IsClosed D) {Δ : Set Y} (hΔ : IsCompact Δ)
    (hDΔ : ∀ z ∈ D, z.2 ∈ Δ) : IsClosed (Prod.fst '' D) := by
  haveI : CompactSpace Δ := isCompact_iff_compactSpace.mp hΔ
  let D' : Set (X × Δ) := {z | (z.1, (z.2 : Y)) ∈ D}
  have hD' : IsClosed D' :=
    hD.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have e : Prod.fst '' D' = Prod.fst '' D := by
    ext x; constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨(z.1, z.2), hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨(z.1, ⟨z.2, hDΔ z hz⟩), hz, rfl⟩
  rw [← e]
  exact isClosedMap_fst_of_compactSpace D' hD'

variable [MeasurableSpace X] [OpensMeasurableSpace X]

lemma mval_meas (hC : IsClosed C) (hκ : ∀ k, Continuous (κ k)) {Δ : Set Y} (hΔ : IsCompact Δ)
    (hCΔ : ∀ z ∈ C, z.2 ∈ Δ) {A : Set X} (hA : MeasurableSet A)
    (hne : ∀ x ∈ A, (fib C κ 0 x).Nonempty) :
    ∀ k (c : ℝ), MeasurableSet (A ∩ {x | mval C κ k x ≤ c}) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro c
  let P : (Fin k → ℚ) → Set X := fun r =>
    Prod.fst '' {z | z ∈ C ∧ κ k z ≤ c ∧ ∀ j : Fin k, κ j z ≤ r j}
  have hP : ∀ r, IsClosed (P r) := by
    intro r
    refine proj_closed ?_ hΔ (fun z hz => hCΔ z hz.1)
    have eS : {z | z ∈ C ∧ κ k z ≤ c ∧ ∀ j : Fin k, κ j z ≤ r j} =
        C ∩ ({z | κ k z ≤ c} ∩ ⋂ j : Fin k, {z | κ j z ≤ r j}) := by
      ext z; simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [eS]
    exact hC.inter ((isClosed_le (hκ k) continuous_const).inter
      (isClosed_iInter fun j => isClosed_le (hκ j) continuous_const))
  have e : A ∩ {x | mval C κ k x ≤ c} = A ∩ ⋂ n : ℕ, ⋃ r : Fin k → ℚ,
      ((⋂ j : Fin k, (A \ (A ∩ {x | mval C κ j x ≤ r j - 1 / ((n : ℝ) + 1)}))) ∩ P r) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_sdiff, not_and, not_le]
    constructor
    · rintro ⟨hxA, hm⟩
      refine ⟨hxA, fun n => ?_⟩
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨y, hy⟩ := fib_nonempty hC hκ hΔ hCΔ (hne x hxA) (k + 1)
      have hy' := (mem_fib C κ (k + 1) x y).mp hy
      have hr : ∀ j : Fin k, ∃ r : ℚ, mval C κ j x < r ∧ (r : ℝ) < mval C κ j x + 1 / ((n : ℝ) + 1) :=
        fun j => exists_rat_btwn (by linarith)
      choose r hr using hr
      refine ⟨r, fun j => ⟨hxA, fun _ => by linarith [(hr j).2]⟩, ⟨(x, y), ⟨hy'.1, ?_, fun j => ?_⟩, rfl⟩⟩
      · exact (hy'.2 k (by omega)).trans hm
      · exact (hy'.2 j (by omega)).trans (hr j).1.le
    · rintro ⟨hxA, h⟩
      refine ⟨hxA, ?_⟩
      let Tn : ℕ → Set Y := fun n => {y | (x, y) ∈ C ∧ κ k (x, y) ≤ c ∧
        ∀ j : Fin k, κ j (x, y) ≤ mval C κ j x + 1 / ((n : ℝ) + 1)}
      have hTd : ∀ n, Tn (n + 1) ⊆ Tn n := by
        intro n y ⟨h1, h2, h3⟩
        refine ⟨h1, h2, fun j => (h3 j).trans ?_⟩
        have : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity); push_cast; linarith
        linarith
      have hTn : ∀ n, (Tn n).Nonempty := by
        intro n
        obtain ⟨r, hr, ⟨z, ⟨hz1, hz2, hz3⟩, hzx⟩⟩ := h n
        obtain ⟨x', y⟩ := z
        simp only at hzx
        subst hzx
        refine ⟨y, hz1, hz2, fun j => (hz3 j).trans ?_⟩
        have := (hr j).2 hxA
        linarith
      have hTcl : ∀ n, IsClosed (Tn n) := by
        intro n
        have eT : Tn n = {y | (x, y) ∈ C} ∩ ({y | κ k (x, y) ≤ c} ∩
            ⋂ j : Fin k, {y | κ j (x, y) ≤ mval C κ j x + 1 / ((n : ℝ) + 1)}) := by
          ext y; simp [Tn]
        rw [eT]
        exact (hC.preimage (Continuous.prodMk_right x)).inter
          ((isClosed_le ((hκ k).comp (Continuous.prodMk_right x)) continuous_const).inter
          (isClosed_iInter fun j =>
            isClosed_le ((hκ j).comp (Continuous.prodMk_right x)) continuous_const))
      have hT0 : IsCompact (Tn 0) :=
        hΔ.of_isClosed_subset (hTcl 0) (fun y hy => hCΔ (x, y) hy.1)
      obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Tn hTd
        hTn hT0 hTcl
      rw [Set.mem_iInter] at hy
      have hyC : (x, y) ∈ C := (hy 0).1
      have hyk : κ k (x, y) ≤ c := (hy 0).2.1
      have hyj : ∀ j : Fin k, κ j (x, y) ≤ mval C κ j x := by
        intro j
        by_contra hlt
        push Not at hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        have := (hy n).2.2 j
        linarith
      have hyf : y ∈ fib C κ k x :=
        (mem_fib C κ k x y).mpr ⟨hyC, fun j hj => hyj ⟨j, hj⟩⟩
      exact (mval_le hC hκ hΔ hCΔ hyf).trans hyk
  rw [e]
  refine hA.inter (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun r => ?_)
  refine (MeasurableSet.iInter fun j : Fin k => hA.diff (IH j.1 j.2 _)).inter (hP r).measurableSet

open Classical in
lemma ext_meas {A : Set X} (hA : MeasurableSet A) {f : X → ℝ}
    (hf : ∀ c : ℝ, MeasurableSet (A ∩ {x | f x ≤ c})) :
    Measurable fun x => if x ∈ A then f x else 0 := by
  classical
  refine measurable_of_Iic fun c => ?_
  have e : (fun x => if x ∈ A then f x else 0) ⁻¹' Set.Iic c =
      (A ∩ {x | f x ≤ c}) ∪ (Aᶜ ∩ {_x | (0 : ℝ) ≤ c}) := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [e]
  exact (hf c).union (hA.compl.inter (MeasurableSet.const _))

end LexSel

/-! ### Basic facts about the program (2.3) (shared with Lemma C.34) -/

namespace D1

open Matrix MeasureTheory IAFTRL

variable {d K : ℕ}

lemma gram_bil {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) (u v : Fin r → ℝ) :
    u ⬝ᵥ ((∑ c, n c • vecMulVec (X c) (X c)) *ᵥ v) = ∑ c, n c * ((X c ⬝ᵥ u) * (X c ⬝ᵥ v)) := by
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, op_smul_eq_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dotProduct_comm u (X c)]
  ring

lemma gram_herm {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) :
    (∑ c, n c • vecMulVec (X c) (X c)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply, mul_comm]

lemma eq_zero_of_orth (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤) (w : Fin d → ℝ)
    (h : ∀ c, arms c ⬝ᵥ w = 0) : w = 0 := by
  have : ∀ v ∈ Submodule.span ℝ (Set.range arms), v ⬝ᵥ w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact h c
    | zero => simp
    | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
    | smul t x _ hx => rw [smul_dotProduct, hx, smul_zero]
  have hw := this w (by rw [hspan]; trivial)
  exact dotProduct_self_eq_zero.mp hw

lemma M_pd (arms : Fin K → Fin d → ℝ) (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (p : Fin K → ℝ) (hp : ∀ b, 0 < p b) :
    (BanditAlgorithm.linearAllocationMatrix arms p).PosDef := by
  have hherm : (BanditAlgorithm.linearAllocationMatrix arms p).IsHermitian := by
    unfold BanditAlgorithm.linearAllocationMatrix; exact gram_herm arms p
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun v hv => ?_
  rw [star_trivial]
  unfold BanditAlgorithm.linearAllocationMatrix
  rw [gram_bil]
  by_contra hle
  push Not at hle
  have hz : ∀ c, arms c ⬝ᵥ v = 0 := by
    intro c
    have hnn : ∀ b ∈ Finset.univ, 0 ≤ p b * ((arms b ⬝ᵥ v) * (arms b ⬝ᵥ v)) :=
      fun b _ => mul_nonneg (hp b).le (mul_self_nonneg _)
    have h0 : ∑ b, p b * ((arms b ⬝ᵥ v) * (arms b ⬝ᵥ v)) = 0 :=
      le_antisymm hle (Finset.sum_nonneg hnn)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 c (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (hp c).ne'
    · exact mul_self_eq_zero.mp h
  exact hv (eq_zero_of_orth arms hspan v hz)

lemma qSoft_pos (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (a : Fin K) :
    0 < qSoft β arms S a := by
  unfold qSoft
  exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨a, Finset.mem_univ _⟩)

lemma qSoft_sum (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (hK : 1 ≤ K) :
    ∑ a, qSoft β arms S a = 1 := by
  unfold qSoft
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨⟨0, hK⟩, Finset.mem_univ _⟩).ne'

lemma beta_ge (hd : 1 ≤ d) (s : ℕ) : 16 * (d : ℝ) ≤ beta d K s := by
  unfold beta; have := Real.sqrt_nonneg ((d : ℝ) * s / (1 + Real.log K)); linarith

lemma beta_pos (hd : 1 ≤ d) (s : ℕ) : 0 < beta d K s := by
  have := beta_ge (K := K) hd s
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma Gam_nonneg (hd : 1 ≤ d) (s : ℕ) : 0 ≤ Gam d K s := by
  unfold Gam; have := beta_pos (K := K) hd s; positivity

lemma Gam_le (hd : 1 ≤ d) (s : ℕ) : Gam d K s ≤ 1 / 4 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hβ := beta_ge (K := K) hd s
  unfold Gam
  rw [div_le_iff₀ (by linarith)]; linarith

lemma p_lower (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (s : ℕ) (S : Fin d → ℝ) (p : Fin K → ℝ)
    (hp : IsFeasible2_3 arms s S p) (b : Fin K) :
    (3 / 4) * qSoft (beta d K s) arms S b ≤ p b := by
  obtain ⟨-, -, ⟨w, hw0, hwΓ, hpw⟩, -⟩ := hp
  have hΓ := Gam_le (K := K) hd s
  have hpb : p b = (1 - ∑ c, w c) * qSoft (beta d K s) arms S b + w b := by rw [hpw]
  rw [hpb]
  have hq := qSoft_pos (beta d K s) arms S b
  have := hw0 b
  nlinarith

lemma refArm_min (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (j : Fin K) :
    ∃ j₀, refArm arms S = arms j₀ ∧ ∀ i, arms j₀ ⬝ᵥ S ≤ arms i ⬝ᵥ S := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ (fun i => arms i ⬝ᵥ S)
    ⟨j, Finset.mem_univ _⟩
  have hne : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty :=
    ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hm i (Finset.mem_univ _)⟩⟩
  refine ⟨_, ?_, (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2⟩
  unfold refArm
  rw [dif_pos hne]

lemma Zd_nonneg (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (b : Fin K) : 0 ≤ Zd arms S b := by
  obtain ⟨j₀, hr, hj₀⟩ := refArm_min arms S b
  unfold Zd; rw [hr]; linarith [hj₀ b]

noncomputable def Wb (d K : ℕ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => Wb d K s + 2 * (beta d K (s + 1) + Wb d K s / Bc K)

lemma Bc_pos (hK : 1 ≤ K) : 0 < Bc K := by
  unfold Bc
  have h2K : (1 : ℝ) ≤ 2 * K := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hl := Real.log_nonneg h2K
  have hc := Int.le_ceil (256 + Real.log (2 * (K : ℝ)))
  have : (0 : ℝ) < (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) := by linarith
  positivity

lemma gap_step (arms : Fin K → Fin d → ℝ) (S θh : Fin d → ℝ) (β B w : ℝ) (hB : 0 < B)
    (hw : ∀ c, Zd arms S c ≤ w)
    (hrow : ∀ c, |(arms c - refArm arms S) ⬝ᵥ θh| ≤ β + Zd arms S c / B) (b : Fin K) :
    Zd arms (S + θh) b ≤ w + 2 * (β + w / B) := by
  obtain ⟨j₁, hr1, -⟩ := refArm_min arms (S + θh) b
  obtain ⟨j₀, hr0, hj₀⟩ := refArm_min arms S b
  have hZ : ∀ c, Zd arms S c = (arms c - arms j₀) ⬝ᵥ S := fun c => by
    unfold Zd; rw [hr0, sub_dotProduct]
  have e : Zd arms (S + θh) b = (Zd arms S b - Zd arms S j₁) +
      ((arms b - refArm arms S) ⬝ᵥ θh - (arms j₁ - refArm arms S) ⬝ᵥ θh) := by
    rw [hZ, hZ]
    unfold Zd
    rw [hr1, hr0]
    simp only [dotProduct_add, sub_dotProduct]
    ring
  rw [e]
  have h1 := hw b
  have h2 := Zd_nonneg arms S j₁
  have h3 := hrow b
  have h4 := hrow j₁
  have h5 : Zd arms S b / B ≤ w / B := div_le_div_of_nonneg_right (hw b) hB.le
  have h6 : Zd arms S j₁ / B ≤ w / B := div_le_div_of_nonneg_right (hw j₁) hB.le
  have := abs_sub ((arms b - refArm arms S) ⬝ᵥ θh) ((arms j₁ - refArm arms S) ⬝ᵥ θh)
  have := le_abs_self ((arms b - refArm arms S) ⬝ᵥ θh - (arms j₁ - refArm arms S) ⬝ᵥ θh)
  linarith

lemma gap_env {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hK : 1 ≤ K)
    (arms : Fin K → Fin d → ℝ) (T : ℕ) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) :
    ∀ t ≤ T, ∀ ω b, Zd arms (R.cumEst arms t ω) b ≤ Wb d K t := by
  intro t
  induction t with
  | zero =>
    intro _ ω b
    have hS : R.cumEst arms 0 ω = 0 := by simp [Run.cumEst]
    rw [hS]
    have : Zd arms 0 b = 0 := by unfold Zd; simp
    rw [this]; simp [Wb]
  | succ s ih =>
    intro hs ω b
    have ih' := ih (by omega) ω
    have hfe := ((hR s (by omega)).2.1.2 ω).1
    obtain ⟨-, -, -, hd3, -⟩ := hfe
    have hS : R.cumEst arms (s + 1) ω = R.cumEst arms s ω + R.thetaHat arms s ω := by
      simp [Run.cumEst, Finset.sum_range_succ]
    rw [hS]
    simp only [Wb]
    refine gap_step arms _ _ (beta d K (s + 1)) (Bc K) (Wb d K s) (Bc_pos hK) ih' (fun c => ?_) b
    unfold Run.thetaHat
    rw [dotProduct_smul, smul_eq_mul, abs_mul]
    have hY : |R.Y s ω| ≤ 1 := (hR s (by omega)).2.2.2.1.1 ω
    have h := hd3 c (R.A s ω)
    have h0 := abs_nonneg ((arms c - refArm arms (R.cumEst arms s ω)) ⬝ᵥ
      vCoef arms (R.p s ω) (R.A s ω))
    nlinarith [abs_nonneg (R.Y s ω)]

lemma meas_vCoef (arms : Fin K → Fin d → ℝ) (b : Fin K) :
    Measurable (fun p : Fin K → ℝ => vCoef arms p b) := by
  have hM : Continuous (fun p : Fin K → ℝ => BanditAlgorithm.linearAllocationMatrix arms p) := by
    unfold BanditAlgorithm.linearAllocationMatrix
    exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  have e : (fun p : Fin K → ℝ => vCoef arms p b) = fun p =>
      (BanditAlgorithm.linearAllocationMatrix arms p).det⁻¹ •
        ((BanditAlgorithm.linearAllocationMatrix arms p).adjugate *ᵥ arms b) := by
    funext p
    unfold vCoef
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec]
  rw [e]
  exact (hM.matrix_det.measurable.inv).smul
    ((hM.matrix_adjugate.matrix_mulVec continuous_const).measurable)

lemma meas_v {Ω : Type*} {m : MeasurableSpace Ω} (arms : Fin K → Fin d → ℝ)
    (p : Ω → Fin K → ℝ) (A : Ω → Fin K) (hp : Measurable[m] p) (hA : Measurable[m] A) :
    Measurable[m] (fun ω => vCoef arms (p ω) (A ω)) := by
  have h2 : Measurable (fun q : (Fin K → ℝ) × Fin K => vCoef arms q.1 q.2) :=
    measurable_from_prod_countable_left fun b => meas_vCoef arms b
  have hv := h2.comp (hp.prodMk hA)
  dsimp only [Function.comp_def] at hv
  exact hv

lemma K_pos (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤) : 1 ≤ K := by
  by_contra h
  have hK : K = 0 := by omega
  subst hK
  have hr : Set.range arms = ∅ := Set.range_eq_empty arms
  rw [hr, Submodule.span_empty] at hspan
  have hmem : (Pi.single ⟨0, hd⟩ (1 : ℝ) : Fin d → ℝ) ∈ (⊥ : Submodule ℝ (Fin d → ℝ)) := by
    rw [hspan]; trivial
  rw [Submodule.mem_bot] at hmem
  have := congrFun hmem ⟨0, hd⟩
  simp at this

end D1

/-! ### The program (2.3) on a piece of constant reference arm -/

namespace D1

open Matrix MeasureTheory IAFTRL

variable {d K : ℕ}

/-- the pieces on which the reference arm is `arms j` -/
def Qp (arms : Fin K → Fin d → ℝ) (j : Fin K) : Set (Fin d → ℝ) :=
  {S | (∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S) ∧ ∀ i, i < j → arms j ⬝ᵥ S < arms i ⬝ᵥ S}

lemma Qp_meas (arms : Fin K → Fin d → ℝ) (j : Fin K) : MeasurableSet (Qp arms j) := by
  have hc : ∀ i : Fin K, Continuous fun S : Fin d → ℝ => arms i ⬝ᵥ S :=
    fun i => continuous_const.dotProduct continuous_id
  have e : Qp arms j = (⋂ i, {S | arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S}) ∩
      ⋂ i, {S | i < j → arms j ⬝ᵥ S < arms i ⬝ᵥ S} := by
    ext S; simp [Qp]
  rw [e]
  refine (MeasurableSet.iInter fun i => measurableSet_le (hc j).measurable (hc i).measurable).inter
    (MeasurableSet.iInter fun i => ?_)
  by_cases h : i < j
  · simp only [h, true_implies]
    exact measurableSet_lt (hc j).measurable (hc i).measurable
  · simp [h]

lemma refArm_of_Qp (arms : Fin K → Fin d → ℝ) {j : Fin K} {S : Fin d → ℝ} (hS : S ∈ Qp arms j) :
    refArm arms S = arms j := by
  classical
  have hmem : j ∈ Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS.1⟩
  have hne : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty :=
    ⟨j, hmem⟩
  unfold refArm
  rw [dif_pos hne]
  congr 1
  apply le_antisymm (Finset.min'_le _ _ hmem)
  by_contra hlt
  push Not at hlt
  have hm := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2 j
  have := hS.2 _ hlt
  linarith

lemma Qp_cover (arms : Fin K → Fin d → ℝ) (hK : 1 ≤ K) (S : Fin d → ℝ) : ∃ j, S ∈ Qp arms j := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ (fun i => arms i ⬝ᵥ S)
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hne : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty :=
    ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hm i (Finset.mem_univ _)⟩⟩
  set j := (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).min' hne
  have hj := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  refine ⟨j, hj, fun i hi => ?_⟩
  by_contra hle
  push Not at hle
  have hi' : i ∈ Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l => hle.trans (hj l)⟩
  have := Finset.min'_le _ _ hi'
  exact absurd hi (not_lt.mpr this)

lemma Qp_disj (arms : Fin K → Fin d → ℝ) {j j' : Fin K} {S : Fin d → ℝ} (h : S ∈ Qp arms j)
    (h' : S ∈ Qp arms j') : j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · have := h'.2 j hlt; have := h.1 j'; linarith
  · exact heq
  · have := h.2 j' hgt; have := h'.1 j; linarith

/-- explicit inverse-times-vector -/
lemma inv_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    M⁻¹ *ᵥ v = M.det⁻¹ • (M.adjugate *ᵥ v) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec]

/-- the closed constraint set of (2.3) with reference arm `arms j` -/
def Cset (arms : Fin K → Fin d → ℝ) (t : ℕ) (j : Fin K) : Set ((Fin d → ℝ) × (Fin K → ℝ)) :=
  {z | (∀ b, 0 ≤ z.2 b) ∧ ∑ b, z.2 b = 1 ∧
      ∀ a, (1 - Gam d K t) * qSoft (beta d K t) arms z.1 a ≤ z.2 a} ∩
  ((⋂ a, ⋂ b, {z | |(arms a - arms j) ⬝ᵥ vCoef arms z.2 b| ≤
      beta d K t + (arms a ⬝ᵥ z.1 - arms j ⬝ᵥ z.1) / Bc K}) ∩
   ((⋂ a, {z | (arms a - arms j) ⬝ᵥ
        (BanditAlgorithm.linearAllocationMatrix arms z.2)⁻¹ *ᵥ (arms a - arms j) ≤
      beta d K t + (arms a ⬝ᵥ z.1 - arms j ⬝ᵥ z.1) ^ 2 / (Bc K * t)}) ∩
    {z | proxyC arms t z.1 z.2 ≤ 2 * (d : ℝ) / beta d K t}))

lemma feas_iff (hd : 1 ≤ d) (hK : 1 ≤ K) (arms : Fin K → Fin d → ℝ) (t : ℕ) {j : Fin K}
    {S : Fin d → ℝ} (hS : S ∈ Qp arms j) (p : Fin K → ℝ) :
    IsFeasible2_3 arms t S p ↔ (S, p) ∈ Cset arms t j := by
  have hr := refArm_of_Qp arms hS
  have hZ : ∀ a, Zd arms S a = arms a ⬝ᵥ S - arms j ⬝ᵥ S := fun a => by unfold Zd; rw [hr]
  have hΓ0 := Gam_nonneg (K := K) hd t
  have hΓ1 := Gam_le (K := K) hd t
  have hq1 := qSoft_sum (beta d K t) arms S hK
  unfold IsFeasible2_3 Cset
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, hr, hZ]
  constructor
  · rintro ⟨h0, h1, ⟨w, hw0, hwΓ, hpw⟩, h3, h4, h5⟩
    refine ⟨⟨h0, h1, fun a => ?_⟩, h3, h4, h5⟩
    have hpa : p a = (1 - ∑ c, w c) * qSoft (beta d K t) arms S a + w a := by rw [hpw]
    rw [hpa]
    have hq := qSoft_pos (beta d K t) arms S a
    have := hw0 a
    nlinarith
  · rintro ⟨⟨h0, h1, h2⟩, h3, h4, h5⟩
    refine ⟨h0, h1, ⟨fun a => p a - (1 - Gam d K t) * qSoft (beta d K t) arms S a,
      fun a => by linarith [h2 a], ?_, ?_⟩, h3, h4, h5⟩
    · have : ∑ a, (p a - (1 - Gam d K t) * qSoft (beta d K t) arms S a) = Gam d K t := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1, hq1]; ring
      rw [this]
    · have : ∑ a, (p a - (1 - Gam d K t) * qSoft (beta d K t) arms S a) = Gam d K t := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1, hq1]; ring
      funext a
      rw [this]; ring

/-! #### Closedness -/

lemma cl_iInter {Z ι : Type*} [TopologicalSpace Z] {E : Set Z} (hE : IsClosed E) {T : ι → Set Z}
    (h : ∀ i, IsClosed (E ∩ T i)) : IsClosed (E ∩ ⋂ i, T i) := by
  have e : E ∩ ⋂ i, T i = E ∩ ⋂ i, (E ∩ T i) := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => ⟨h1, h2 i⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => (h2 i).2⟩
  rw [e]; exact hE.inter (isClosed_iInter h)

lemma cl_le {Z : Type*} [TopologicalSpace Z] {E : Set Z} (hE : IsClosed E) {f g : Z → ℝ}
    (hf : ContinuousOn f E) (hg : ContinuousOn g E) : IsClosed (E ∩ {z | f z ≤ g z}) :=
  (hf.prodMk hg).preimage_isClosed_of_isClosed hE (isClosed_le continuous_fst continuous_snd)

lemma qSoft_cont (β : ℝ) (arms : Fin K → Fin d → ℝ) (a : Fin K) :
    Continuous fun S : Fin d → ℝ => qSoft β arms S a := by
  unfold qSoft
  refine Continuous.div ?_ ?_ fun S => ?_
  · exact ((continuous_const.dotProduct continuous_id).neg.div_const _).rexp
  · exact continuous_finsetSum _ fun b _ =>
      ((continuous_const.dotProduct continuous_id).neg.div_const _).rexp
  · by_cases hK : (Finset.univ : Finset (Fin K)).Nonempty
    · exact (Finset.sum_pos (fun b _ => Real.exp_pos _) hK).ne'
    · exact absurd ⟨a, Finset.mem_univ _⟩ hK

lemma Cset_closed (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤) (t : ℕ) (j : Fin K) :
    IsClosed (Cset arms t j) := by
  set E : Set ((Fin d → ℝ) × (Fin K → ℝ)) := {z | (∀ b, 0 ≤ z.2 b) ∧ ∑ b, z.2 b = 1 ∧
      ∀ a, (1 - Gam d K t) * qSoft (beta d K t) arms z.1 a ≤ z.2 a} with hEdef
  have hE : IsClosed E := by
    have e : E = (⋂ b, {z : (Fin d → ℝ) × (Fin K → ℝ) | 0 ≤ z.2 b}) ∩
        ({z | ∑ b, z.2 b = 1} ∩ ⋂ a, {z | (1 - Gam d K t) * qSoft (beta d K t) arms z.1 a ≤ z.2 a}) := by
      ext z; simp [hEdef]
    rw [e]
    refine (isClosed_iInter fun b => isClosed_le continuous_const
      ((continuous_apply b).comp continuous_snd)).inter
      ((isClosed_eq (continuous_finsetSum _ fun b _ => (continuous_apply b).comp continuous_snd)
        continuous_const).inter (isClosed_iInter fun a => isClosed_le
          (continuous_const.mul ((qSoft_cont _ arms a).comp continuous_fst))
          ((continuous_apply a).comp continuous_snd)))
  -- on `E` the design matrix is invertible
  have hpos : ∀ z ∈ E, ∀ b, 0 < z.2 b := by
    intro z hz b
    have hq := qSoft_pos (beta d K t) arms z.1 b
    have hΓ := Gam_le (K := K) hd t
    have := hz.2.2 b
    nlinarith
  have hdet : ∀ z ∈ E, (BanditAlgorithm.linearAllocationMatrix arms z.2).det ≠ 0 :=
    fun z hz => (M_pd arms hspan z.2 (hpos z hz)).det_pos.ne'
  have hM : Continuous fun z : (Fin d → ℝ) × (Fin K → ℝ) =>
      BanditAlgorithm.linearAllocationMatrix arms z.2 := by
    unfold BanditAlgorithm.linearAllocationMatrix
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp continuous_snd).smul continuous_const
  have hinv : ∀ v : Fin d → ℝ, ContinuousOn (fun z : (Fin d → ℝ) × (Fin K → ℝ) =>
      (BanditAlgorithm.linearAllocationMatrix arms z.2)⁻¹ *ᵥ v) E := by
    intro v
    have e : (fun z : (Fin d → ℝ) × (Fin K → ℝ) =>
        (BanditAlgorithm.linearAllocationMatrix arms z.2)⁻¹ *ᵥ v) = fun z =>
        (BanditAlgorithm.linearAllocationMatrix arms z.2).det⁻¹ •
          ((BanditAlgorithm.linearAllocationMatrix arms z.2).adjugate *ᵥ v) := by
      funext z; exact inv_mulVec _ v
    rw [e]
    exact (hM.matrix_det.continuousOn.inv₀ hdet).smul
      (hM.matrix_adjugate.matrix_mulVec continuous_const).continuousOn
  have hv : ∀ b, ContinuousOn (fun z : (Fin d → ℝ) × (Fin K → ℝ) => vCoef arms z.2 b) E := by
    intro b; unfold vCoef; exact hinv (arms b)
  have hdotS : ∀ x : Fin d → ℝ, Continuous fun z : (Fin d → ℝ) × (Fin K → ℝ) => x ⬝ᵥ z.1 :=
    fun x => continuous_const.dotProduct continuous_fst
  have hβ := beta_pos (K := K) hd t
  -- the three groups of constraints
  have h3 : IsClosed (E ∩ ⋂ a, ⋂ b, {z : (Fin d → ℝ) × (Fin K → ℝ) |
      |(arms a - arms j) ⬝ᵥ vCoef arms z.2 b| ≤
        beta d K t + (arms a ⬝ᵥ z.1 - arms j ⬝ᵥ z.1) / Bc K}) := by
    refine cl_iInter hE fun a => cl_iInter hE fun b => cl_le hE ?_ ?_
    · exact (continuous_abs.comp_continuousOn
        ((continuous_const.dotProduct continuous_id).comp_continuousOn (hv b)))
    · exact (continuous_const.add (((hdotS _).sub (hdotS _)).div_const _)).continuousOn
  have h4 : IsClosed (E ∩ ⋂ a, {z : (Fin d → ℝ) × (Fin K → ℝ) | (arms a - arms j) ⬝ᵥ
        (BanditAlgorithm.linearAllocationMatrix arms z.2)⁻¹ *ᵥ (arms a - arms j) ≤
      beta d K t + (arms a ⬝ᵥ z.1 - arms j ⬝ᵥ z.1) ^ 2 / (Bc K * t)}) := by
    refine cl_iInter hE fun a => cl_le hE ?_ ?_
    · exact (continuous_const.dotProduct continuous_id).comp_continuousOn (hinv _)
    · exact (continuous_const.add ((((hdotS _).sub (hdotS _)).pow 2).div_const _)).continuousOn
  have h5 : IsClosed (E ∩ {z : (Fin d → ℝ) × (Fin K → ℝ) |
      proxyC arms t z.1 z.2 ≤ 2 * (d : ℝ) / beta d K t}) := by
    refine cl_le hE ?_ continuousOn_const
    unfold proxyC
    refine continuousOn_const.mul (continuousOn_finset_sum _ fun b _ => ?_)
    refine ((continuous_apply b).comp continuous_snd).continuousOn.mul
      (continuousOn_finset_sum _ fun a _ => ?_)
    refine ((qSoft_cont _ arms a).comp continuous_fst).continuousOn.mul ?_
    have hchi : Continuous chi := by
      unfold chi; fun_prop
    refine hchi.comp_continuousOn (ContinuousOn.div_const ?_ _)
    have hab : Continuous fun z : (Fin d → ℝ) × (Fin K → ℝ) =>
        arms a - abar arms (qSoft (beta d K t) arms z.1) := by
      unfold abar
      exact continuous_const.sub (continuous_finsetSum _ fun c _ =>
        ((qSoft_cont _ arms c).comp continuous_fst).smul continuous_const)
    exact (continuous_fst.dotProduct continuous_snd).comp_continuousOn
      (hab.continuousOn.prodMk (hv b))
  have e : Cset arms t j = (E ∩ ⋂ a, ⋂ b, {z : (Fin d → ℝ) × (Fin K → ℝ) |
      |(arms a - arms j) ⬝ᵥ vCoef arms z.2 b| ≤
        beta d K t + (arms a ⬝ᵥ z.1 - arms j ⬝ᵥ z.1) / Bc K}) ∩
      ((E ∩ ⋂ a, {z : (Fin d → ℝ) × (Fin K → ℝ) | (arms a - arms j) ⬝ᵥ
        (BanditAlgorithm.linearAllocationMatrix arms z.2)⁻¹ *ᵥ (arms a - arms j) ≤
      beta d K t + (arms a ⬝ᵥ z.1 - arms j ⬝ᵥ z.1) ^ 2 / (Bc K * t)}) ∩
      (E ∩ {z : (Fin d → ℝ) × (Fin K → ℝ) |
        proxyC arms t z.1 z.2 ≤ 2 * (d : ℝ) / beta d K t})) := by
    unfold Cset
    rw [← hEdef]
    ext z
    simp only [Set.mem_inter_iff]
    tauto
  rw [e]
  exact h3.inter (h4.inter h5)

end D1

/-! ### Measurable lexicographic selection and integrability -/

namespace D1

open Matrix MeasureTheory IAFTRL

variable {d K : ℕ}

/-- the objective of (2.3) with reference arm `arms j` -/
noncomputable def obj (arms : Fin K → Fin d → ℝ) (t : ℕ) (j : Fin K)
    (z : (Fin d → ℝ) × (Fin K → ℝ)) : ℝ :=
  ∑ a, z.2 a * min 2 ((arms a ⬝ᵥ z.1 - arms j ⬝ᵥ z.1) / t)

/-- lexicographic keys: the objective, then the coordinates in the order of `Fin K` -/
noncomputable def keys (arms : Fin K → Fin d → ℝ) (t : ℕ) (j : Fin K) :
    ℕ → (Fin d → ℝ) × (Fin K → ℝ) → ℝ
  | 0 => obj arms t j
  | i + 1 => fun z => if h : i < K then z.2 ⟨i, h⟩ else 0

lemma keys_zero (arms : Fin K → Fin d → ℝ) (t : ℕ) (j : Fin K) (z : (Fin d → ℝ) × (Fin K → ℝ)) :
    keys arms t j 0 z = obj arms t j z := rfl

lemma keys_succ (arms : Fin K → Fin d → ℝ) (t : ℕ) (j : Fin K) (z : (Fin d → ℝ) × (Fin K → ℝ))
    (i : Fin K) : keys arms t j (i.val + 1) z = z.2 i := by
  show (if h : (i : ℕ) < K then z.2 ⟨i, h⟩ else 0) = z.2 i
  rw [dif_pos i.isLt]

lemma keys_cont (arms : Fin K → Fin d → ℝ) (t : ℕ) (j : Fin K) :
    ∀ k, Continuous (keys arms t j k)
  | 0 => by
      show Continuous (obj arms t j)
      unfold obj
      exact continuous_finsetSum _ fun a _ => ((continuous_apply a).comp continuous_snd).mul
        (continuous_const.min (((continuous_const.dotProduct continuous_fst).sub
          (continuous_const.dotProduct continuous_fst)).div_const _))
  | i + 1 => by
      show Continuous fun z : (Fin d → ℝ) × (Fin K → ℝ) => if h : i < K then z.2 ⟨i, h⟩ else 0
      by_cases h : i < K
      · simp only [dif_pos h]; exact (continuous_apply _).comp continuous_snd
      · simp only [dif_neg h]; exact continuous_const

lemma obj_eq (arms : Fin K → Fin d → ℝ) (t : ℕ) {j : Fin K} {S : Fin d → ℝ}
    (hS : S ∈ Qp arms j) (p : Fin K → ℝ) :
    obj arms t j (S, p) = ∑ a, p a * gapHat arms t S a := by
  unfold obj gapHat Zd
  rw [refArm_of_Qp arms hS]

theorem sel_exists (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms) (t : ℕ)
    (ht : 1 ≤ t) :
    ∃ sel : (Fin d → ℝ) → (Fin K → ℝ), Measurable sel ∧
      ∀ S, IsMin2_3 arms t S (sel S) ∧
        ∀ p : Fin K → ℝ, IsMin2_3 arms t S p → toLex (sel S) ≤ toLex p := by
  classical
  have hspan := hA.2.2
  have hK := K_pos hd arms hspan
  obtain ⟨π, hπ⟩ := IAFTRL.lemma_J_3_finite hd arms hspan
  have hΔ : IsCompact (stdSimplex ℝ (Fin K)) := isCompact_stdSimplex ℝ (Fin K)
  have hCΔ : ∀ j, ∀ z ∈ Cset arms t j, z.2 ∈ stdSimplex ℝ (Fin K) :=
    fun j z hz => ⟨hz.1.1, hz.1.2.1⟩
  have hcl : ∀ j, IsClosed (Cset arms t j) := Cset_closed hd arms hspan t
  have hκ : ∀ j, ∀ k, Continuous (keys arms t j k) := keys_cont arms t
  have hne : ∀ j, ∀ S ∈ Qp arms j,
      (LexSel.fib (Cset arms t j) (keys arms t j) 0 S).Nonempty := by
    intro j S hS
    have hf := (IAFTRL.lemma_D_10 hd arms hA t ht S π hπ).1
    exact ⟨_, (feas_iff hd hK arms t hS _).mp hf⟩
  let g : Fin K → ℕ → (Fin d → ℝ) → ℝ := fun j k S =>
    if S ∈ Qp arms j then LexSel.mval (Cset arms t j) (keys arms t j) k S else 0
  have hg : ∀ j k, Measurable (g j k) := fun j k =>
    LexSel.ext_meas (Qp_meas arms j)
      (LexSel.mval_meas (hcl j) (hκ j) hΔ (hCΔ j) (Qp_meas arms j) (hne j) k)
  refine ⟨fun S i => ∑ j, g j (i.val + 1) S, ?_, ?_⟩
  · exact measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ => hg j _
  · intro S
    obtain ⟨j, hj⟩ := Qp_cover arms hK S
    have hsel : (fun i : Fin K => ∑ j', g j' (i.val + 1) S) =
        fun i => LexSel.mval (Cset arms t j) (keys arms t j) (i.val + 1) S := by
      funext i
      rw [Finset.sum_eq_single j]
      · simp only [g, if_pos hj]
      · intro j' _ hj'
        simp only [g]
        rw [if_neg]
        intro h; exact hj' (Qp_disj arms h hj)
      · intro h; exact absurd (Finset.mem_univ j) h
    show IsMin2_3 arms t S (fun i : Fin K => ∑ j', g j' (i.val + 1) S) ∧
      ∀ p : Fin K → ℝ, IsMin2_3 arms t S p →
        toLex (fun i : Fin K => ∑ j', g j' (i.val + 1) S) ≤ toLex p
    rw [hsel]
    set ys : Fin K → ℝ := fun i => LexSel.mval (Cset arms t j) (keys arms t j) (i.val + 1) S with hys
    -- a point of the last fibre
    obtain ⟨y, hy⟩ := LexSel.fib_nonempty (hcl j) (hκ j) hΔ (hCΔ j) (hne j S hj) (K + 1)
    have hy' := (LexSel.mem_fib (Cset arms t j) (keys arms t j) (K + 1) S y).mp hy
    have hyl : ∀ l, l ≤ K + 1 → y ∈ LexSel.fib (Cset arms t j) (keys arms t j) l S := fun l hl =>
      (LexSel.mem_fib (Cset arms t j) (keys arms t j) l S y).mpr ⟨hy'.1, fun m hm => hy'.2 m (by omega)⟩
    have hyeq : y = ys := by
      funext i
      have h1 := hy'.2 (i.val + 1) (by omega)
      have h2 := LexSel.mval_le (hcl j) (hκ j) hΔ (hCΔ j) (hyl (i.val + 1) (by omega))
      rw [show keys arms t j (i.val + 1) (S, y) = y i from keys_succ arms t j (S, y) i] at h1 h2
      show y i = LexSel.mval (Cset arms t j) (keys arms t j) (i.val + 1) S
      linarith
    rw [← hyeq]
    have hfeas : IsFeasible2_3 arms t S y := (feas_iff hd hK arms t hj y).mpr hy'.1
    have hobj : obj arms t j (S, y) ≤ LexSel.mval (Cset arms t j) (keys arms t j) 0 S := hy'.2 0 (by omega)
    have hmin : IsMin2_3 arms t S y := by
      refine ⟨hfeas, fun p' hp' => ?_⟩
      have hp'C : (S, p') ∈ Cset arms t j := (feas_iff hd hK arms t hj p').mp hp'
      have hp'f : p' ∈ LexSel.fib (Cset arms t j) (keys arms t j) 0 S := (LexSel.mem_fib (Cset arms t j) (keys arms t j) 0 S p').mpr ⟨hp'C, by simp⟩
      have h1 := LexSel.mval_le (hcl j) (hκ j) hΔ (hCΔ j) hp'f
      rw [show keys arms t j 0 (S, p') = obj arms t j (S, p') from rfl, obj_eq arms t hj] at h1
      rw [obj_eq arms t hj] at hobj
      linarith
    refine ⟨hmin, fun p hp => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨i, hi1, hi2⟩ := hlt
    have hi1' : ∀ l : Fin K, l < i → p l = LexSel.mval (Cset arms t j) (keys arms t j) (l.val + 1) S :=
      fun l hl => by have h := hi1 l hl; rw [hyeq] at h; exact h
    have hi2' : p i < LexSel.mval (Cset arms t j) (keys arms t j) (i.val + 1) S := by
      have h := hi2; rw [hyeq] at h; exact h
    have hpC : (S, p) ∈ Cset arms t j := (feas_iff hd hK arms t hj p).mp hp.1
    have hpf : p ∈ LexSel.fib (Cset arms t j) (keys arms t j) (i.val + 1) S := by
      refine (LexSel.mem_fib (Cset arms t j) (keys arms t j) (i.val + 1) S p).mpr ⟨hpC, fun l hl => ?_⟩
      cases l with
      | zero =>
        have h1 := hp.2 y hfeas
        rw [show keys arms t j 0 (S, p) = obj arms t j (S, p) from rfl, obj_eq arms t hj]
        rw [obj_eq arms t hj] at hobj
        linarith
      | succ l =>
        have hlK : l < K := by have := i.isLt; omega
        rw [show keys arms t j (l + 1) (S, p) = p ⟨l, hlK⟩ from keys_succ arms t j (S, p) ⟨l, hlK⟩]
        rw [hi1' ⟨l, hlK⟩ (by show l < i.val; omega)]
    have h3 := LexSel.mval_le (hcl j) (hκ j) hΔ (hCΔ j) hpf
    rw [show keys arms t j (i.val + 1) (S, p) = p i from keys_succ arms t j (S, p) i] at h3
    linarith

/-! #### Integrability -/

lemma quad_le (arms : Fin K → Fin d → ℝ) (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (p : Fin K → ℝ) (hp : ∀ b, 0 < p b) (a c : Fin K) :
    |arms a ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ *ᵥ arms c| ≤
      (1 / p a + 1 / p c) / 2 := by
  set N := BanditAlgorithm.linearAllocationMatrix arms p with hN
  have hpd := M_pd arms hspan p hp
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hpd.det_pos.ne'
  have hNy : ∀ v, N *ᵥ (N⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hbil : ∀ u v, u ⬝ᵥ (N *ᵥ v) = ∑ b, p b * ((arms b ⬝ᵥ u) * (arms b ⬝ᵥ v)) := fun u v => by
    rw [hN]; unfold BanditAlgorithm.linearAllocationMatrix; exact gram_bil arms p u v
  set y := N⁻¹ *ᵥ arms a with hydef
  set w := N⁻¹ *ᵥ arms c with hwdef
  have hy : N *ᵥ y = arms a := hNy _
  have hw : N *ᵥ w = arms c := hNy _
  have eX : arms a ⬝ᵥ w = ∑ b, p b * ((arms b ⬝ᵥ w) * (arms b ⬝ᵥ y)) := by
    rw [← hy, dotProduct_comm, hbil]
  have eA : arms a ⬝ᵥ y = ∑ b, p b * ((arms b ⬝ᵥ y) * (arms b ⬝ᵥ y)) := by
    rw [← hy, dotProduct_comm, hbil]
  have eC : arms c ⬝ᵥ w = ∑ b, p b * ((arms b ⬝ᵥ w) * (arms b ⬝ᵥ w)) := by
    rw [← hw, dotProduct_comm, hbil]
  set X := ∑ b, p b * ((arms b ⬝ᵥ w) * (arms b ⬝ᵥ y))
  set QA := ∑ b, p b * ((arms b ⬝ᵥ y) * (arms b ⬝ᵥ y))
  set QC := ∑ b, p b * ((arms b ⬝ᵥ w) * (arms b ⬝ᵥ w))
  have h1 : 0 ≤ QA - 2 * X + QC := by
    have : QA - 2 * X + QC = ∑ b, p b * ((arms b ⬝ᵥ y) - (arms b ⬝ᵥ w)) ^ 2 := by
      simp only [QA, X, QC]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this]; exact Finset.sum_nonneg fun b _ => mul_nonneg (hp b).le (sq_nonneg _)
  have h2 : 0 ≤ QA + 2 * X + QC := by
    have : QA + 2 * X + QC = ∑ b, p b * ((arms b ⬝ᵥ y) + (arms b ⬝ᵥ w)) ^ 2 := by
      simp only [QA, X, QC]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this]; exact Finset.sum_nonneg fun b _ => mul_nonneg (hp b).le (sq_nonneg _)
  have hQle : ∀ (e : Fin K) (z : Fin d → ℝ), arms e ⬝ᵥ z = ∑ b, p b * ((arms b ⬝ᵥ z) * (arms b ⬝ᵥ z)) →
      ∑ b, p b * ((arms b ⬝ᵥ z) * (arms b ⬝ᵥ z)) ≤ 1 / p e := by
    intro e z hz
    set Q := ∑ b, p b * ((arms b ⬝ᵥ z) * (arms b ⬝ᵥ z))
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun b _ => mul_nonneg (hp b).le (mul_self_nonneg _)
    have hsingle : p e * ((arms e ⬝ᵥ z) * (arms e ⬝ᵥ z)) ≤ Q :=
      Finset.single_le_sum (f := fun b => p b * ((arms b ⬝ᵥ z) * (arms b ⬝ᵥ z)))
        (fun b _ => mul_nonneg (hp b).le (mul_self_nonneg _)) (Finset.mem_univ e)
    rw [hz] at hsingle
    rw [le_div_iff₀ (hp e)]
    by_cases hQ : Q = 0
    · rw [hQ]; norm_num
    · have hQp : 0 < Q := lt_of_le_of_ne hQ0 (Ne.symm hQ)
      have : p e * Q * Q ≤ 1 * Q := by nlinarith
      have := le_of_mul_le_mul_right this hQp
      linarith
  have hA := hQle a y eA
  have hC := hQle c w eC
  rw [show arms a ⬝ᵥ N⁻¹ *ᵥ arms c = X from eX]
  rw [abs_le]
  constructor <;> linarith

lemma q_lower (β : ℝ) (hβ : 0 < β) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (W : ℝ)
    (hW : ∀ a, Zd arms S a ≤ W) (a : Fin K) :
    Real.exp (-W / β) / K ≤ qSoft β arms S a := by
  obtain ⟨j₀, hr, hj₀⟩ := refArm_min arms S a
  set m := arms j₀ ⬝ᵥ S
  have hK : (0 : ℝ) < K := by
    have : 0 < K := Fin.pos a
    exact_mod_cast this
  have hden : ∑ b, Real.exp (-(arms b ⬝ᵥ S) / β) ≤ K * Real.exp (-m / β) := by
    have : ∀ b ∈ Finset.univ, Real.exp (-(arms b ⬝ᵥ S) / β) ≤ Real.exp (-m / β) := by
      intro b _
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hβ.le
      linarith [hj₀ b]
    calc ∑ b, Real.exp (-(arms b ⬝ᵥ S) / β) ≤ ∑ _b : Fin K, Real.exp (-m / β) :=
          Finset.sum_le_sum this
      _ = K * Real.exp (-m / β) := by simp
  have hdpos : 0 < ∑ b, Real.exp (-(arms b ⬝ᵥ S) / β) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨a, Finset.mem_univ _⟩
  have hZ : Zd arms S a = arms a ⬝ᵥ S - m := by unfold Zd; rw [hr]
  have hnum : Real.exp (-W / β) * Real.exp (-m / β) ≤ Real.exp (-(arms a ⬝ᵥ S) / β) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hW a
    rw [hZ] at this
    rw [← add_div, div_le_div_iff_of_pos_right hβ]
    linarith
  unfold qSoft
  rw [div_le_div_iff₀ hK hdpos]
  have hE := Real.exp_pos (-W / β)
  have hm := Real.exp_pos (-m / β)
  nlinarith [mul_le_mul_of_nonneg_left hden hE.le]

lemma theta_bound (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms) (T : ℕ) (R : Run d K Ω)
    (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t < T) :
    ∃ B : ℝ, ∀ ω (a : Fin K), |arms a ⬝ᵥ R.thetaHat arms t ω| ≤ B := by
  have hspan := hA.2.2
  have hK := K_pos hd arms hspan
  set β := beta d K (t + 1)
  have hβ : 0 < β := beta_pos hd (t + 1)
  set pm : ℝ := (3 / 4) * (Real.exp (-Wb d K t / β) / K)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpm : 0 < pm := by positivity
  refine ⟨1 / pm, fun ω a => ?_⟩
  have hfeas := ((hR t ht).2.1.2 ω).1
  have hW := gap_env P hK arms T R hR t ht.le ω
  have hpl : ∀ b, pm ≤ R.p t ω b := by
    intro b
    have h1 := p_lower hd arms (t + 1) _ _ hfeas b
    have h2 := q_lower β hβ arms (R.cumEst arms t ω) (Wb d K t) hW b
    show (3 / 4) * (Real.exp (-Wb d K t / β) / K) ≤ R.p t ω b
    linarith
  have hppos : ∀ b, 0 < R.p t ω b := fun b => lt_of_lt_of_le hpm (hpl b)
  have hq := quad_le arms hspan (R.p t ω) hppos a (R.A t ω)
  have hinv : ∀ b, 1 / R.p t ω b ≤ 1 / pm := fun b => one_div_le_one_div_of_le hpm (hpl b)
  unfold Run.thetaHat vCoef
  rw [dotProduct_smul, smul_eq_mul, abs_mul]
  have hY : |R.Y t ω| ≤ 1 := (hR t ht).2.2.2.1.1 ω
  have h0 := abs_nonneg (arms a ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms (R.p t ω))⁻¹ *ᵥ
    arms (R.A t ω))
  have h4 : |arms a ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms (R.p t ω))⁻¹ *ᵥ
      arms (R.A t ω)| ≤ 1 / pm := by
    have := hinv a; have := hinv (R.A t ω); linarith
  nlinarith [abs_nonneg (R.Y t ω)]

lemma theta_meas {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (arms : Fin K → Fin d → ℝ) (T : ℕ) (R : Run d K Ω)
    (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t < T) :
    Measurable (R.thetaHat arms t) := by
  obtain ⟨⟨hA, hY, -, hG, hhist, -⟩, ⟨hp, -⟩, -⟩ := hR t ht
  have hp' : Measurable (R.p t) := hp.mono (hhist.trans hG) le_rfl
  unfold Run.thetaHat
  exact hY.smul (meas_v arms (R.p t) (R.A t) hp' hA)

theorem integrability (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) :
    (∀ t < T, Integrable (R.thetaHat arms t) P) ∧
      ∀ t ≤ T, ∀ a c : Fin K,
        Integrable (fun ω => arms a ⬝ᵥ R.cumEst arms t ω - arms c ⬝ᵥ R.cumEst arms t ω) P := by
  have hspan := hA.2.2
  have hK := K_pos hd arms hspan
  constructor
  · intro t ht
    obtain ⟨B, hB⟩ := theta_bound hd P arms hA T R hR t ht
    have hcoef : ∀ i : Fin d, ∃ c : Fin K → ℝ, ∑ a, c a • arms a = Pi.single i 1 := by
      intro i
      have hmem : (Pi.single i (1 : ℝ) : Fin d → ℝ) ∈ Submodule.span ℝ (Set.range arms) := by
        rw [hspan]; trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    choose c hc using hcoef
    have hcomp : ∀ ω (i : Fin d), |R.thetaHat arms t ω i| ≤ ∑ a, |c i a| * |B| := by
      intro ω i
      have e : R.thetaHat arms t ω i = ∑ a, c i a * (arms a ⬝ᵥ R.thetaHat arms t ω) := by
        have h1 : Pi.single i (1 : ℝ) ⬝ᵥ R.thetaHat arms t ω = R.thetaHat arms t ω i := by
          rw [single_dotProduct, one_mul]
        rw [← h1, ← hc i, sum_dotProduct]
        simp only [smul_dotProduct, smul_eq_mul]
      rw [e]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hB ω a).trans (le_abs_self B)) (abs_nonneg _)
    set Cθ := ∑ i, ∑ a, |c i a| * |B|
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ ∑ a, |c i a| * |B| :=
      fun i _ => Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hCθ : 0 ≤ Cθ := Finset.sum_nonneg hnn
    refine Integrable.of_bound (theta_meas P arms T R hR t ht).aestronglyMeasurable Cθ
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [pi_norm_le_iff_of_nonneg hCθ]
    intro i
    rw [Real.norm_eq_abs]
    exact (hcomp ω i).trans (Finset.single_le_sum (f := fun i => ∑ a, |c i a| * |B|) hnn
      (Finset.mem_univ i))
  · intro t ht a c
    have hS : Measurable (R.cumEst arms t) := by
      unfold Run.cumEst
      exact Finset.measurable_sum _ fun s hs =>
        theta_meas P arms T R hR s (by have := Finset.mem_range.mp hs; omega)
    have hmeas : Measurable
        (fun ω => arms a ⬝ᵥ R.cumEst arms t ω - arms c ⬝ᵥ R.cumEst arms t ω) :=
      ((continuous_const.dotProduct continuous_id).measurable.comp hS).sub
        ((continuous_const.dotProduct continuous_id).measurable.comp hS)
    have hW := gap_env P hK arms T R hR t ht
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Wb d K t)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have e : arms a ⬝ᵥ R.cumEst arms t ω - arms c ⬝ᵥ R.cumEst arms t ω =
        Zd arms (R.cumEst arms t ω) a - Zd arms (R.cumEst arms t ω) c := by
      unfold Zd; ring
    rw [e, abs_le]
    have := hW ω a; have := hW ω c
    have := Zd_nonneg arms (R.cumEst arms t ω) a
    have := Zd_nonneg arms (R.cumEst arms t ω) c
    constructor <;> linarith

end D1

namespace IAFTRL

open Matrix MeasureTheory

theorem _root_.solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms) :
    (∀ t : ℕ, 1 ≤ t → ∀ S : Fin d → ℝ, ∃ p : Fin K → ℝ, IsMin2_3 arms t S p) ∧
    (∀ t : ℕ, 1 ≤ t → ∃ sel : (Fin d → ℝ) → (Fin K → ℝ), Measurable sel ∧
      ∀ S, IsMin2_3 arms t S (sel S) ∧
        ∀ p : Fin K → ℝ, IsMin2_3 arms t S p → toLex (sel S) ≤ toLex p) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
      (R : Run d K Ω), IsIAFTRLRun P arms T R →
      (∀ t < T, Integrable (R.thetaHat arms t) P) ∧
      ∀ t ≤ T, ∀ a c : Fin K,
        Integrable (fun ω => arms a ⬝ᵥ R.cumEst arms t ω - arms c ⬝ᵥ R.cumEst arms t ω) P) := by

  refine ⟨fun t ht S => ?_, fun t ht => D1.sel_exists hd arms hA t ht, ?_⟩
  · obtain ⟨sel, -, hsel⟩ := D1.sel_exists hd arms hA t ht
    exact ⟨sel S, (hsel S).1⟩
  · intro Ω _ P _ T R hR
    exact D1.integrability hd arms hA P T R hR

end IAFTRL
