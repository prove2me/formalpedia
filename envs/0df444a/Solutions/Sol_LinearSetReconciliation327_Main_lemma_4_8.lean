-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-16T12:58:43.249904+00:00
-- url     : https://prove2.me/submissions/46e085d7-55c3-4fff-8ad7-f6ff43f0522f

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
set_option autoImplicit false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

noncomputable section

open Classical MeasureTheory ProbabilityTheory

/-! ## Uniform averages: basic lemmas -/

lemma prU_eq_sum (α : Type) [Fintype α] (P : α → Prop) :
    prU P = (∑ a, (if P a then (1 : ℝ) else 0)) / (Fintype.card α : ℝ) := by
  have h : (∑ a, (if P a then (1 : ℝ) else 0)) = ((univ.filter P).card : ℝ) := by
    rw [Finset.sum_boole]
  rw [prU, h]

lemma prU_eq_expU (α : Type) [Fintype α] (P : α → Prop) :
    prU P = expU (fun a => if P a then (1 : ℝ) else 0) := by
  rw [prU_eq_sum, expU]

lemma prU_le_expU {α : Type} [Fintype α] (P : α → Prop) (g : α → ℝ)
    (h : ∀ a, (if P a then (1 : ℝ) else 0) ≤ g a) : prU P ≤ expU g := by
  rw [prU_eq_sum, expU]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

lemma expU_const_mul {α : Type} [Fintype α] [Nonempty α] (c : ℝ) (f : α → ℝ) :
    expU (fun a => c * f a) = c * expU f := by
  rw [expU, expU, ← Finset.mul_sum, mul_div_assoc]

lemma expU_mono {α : Type} [Fintype α] [Nonempty α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expU f ≤ expU g := by
  rw [expU, expU]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

lemma expU_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    expU (fun a => f (e a)) = expU f := by
  rw [expU, expU, Equiv.sum_comp e f, Fintype.card_congr e]

/-! ## Chernoff's trick -/

lemma chernoff {α : Type} [Fintype α] [Nonempty α] (X : α → ℝ) (C : ℝ) (hC : 0 < C)
    (hmgf : ∀ θ : ℝ, 0 < θ → expU (fun a => Real.exp (θ * X a)) ≤ Real.exp (θ ^ 2 * C / 8))
    {t : ℝ} (ht : 0 < t) :
    prU (fun a => t ≤ X a) ≤ Real.exp (-(2 * t ^ 2 / C)) := by
  have hθ : 0 < 4 * t / C := by positivity
  have h1 : prU (fun a => t ≤ X a) ≤ expU (fun a => Real.exp ((4 * t / C) * (X a - t))) := by
    apply prU_le_expU
    intro a
    by_cases ha : t ≤ X a
    · rw [if_pos ha]
      have h0 : 0 ≤ (4 * t / C) * (X a - t) := mul_nonneg hθ.le (by linarith)
      calc (1:ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp ((4 * t / C) * (X a - t)) := Real.exp_le_exp.mpr h0
    · rw [if_neg ha]
      exact (Real.exp_pos _).le
  have h2 : expU (fun a => Real.exp ((4 * t / C) * (X a - t)))
      = Real.exp (-((4 * t / C) * t)) * expU (fun a => Real.exp ((4 * t / C) * X a)) := by
    have heq : (fun a => Real.exp ((4 * t / C) * (X a - t)))
        = (fun a => Real.exp (-((4 * t / C) * t)) * Real.exp ((4 * t / C) * X a)) := by
      funext a; rw [← Real.exp_add]; congr 1; ring
    rw [heq, expU_const_mul]
  have h3 : expU (fun a => Real.exp ((4 * t / C) * X a)) ≤ Real.exp ((4 * t / C) ^ 2 * C / 8) :=
    hmgf _ hθ
  calc prU (fun a => t ≤ X a)
      ≤ expU (fun a => Real.exp ((4 * t / C) * (X a - t))) := h1
    _ = Real.exp (-((4 * t / C) * t)) * expU (fun a => Real.exp ((4 * t / C) * X a)) := h2
    _ ≤ Real.exp (-((4 * t / C) * t)) * Real.exp ((4 * t / C) ^ 2 * C / 8) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp (-(2 * t ^ 2 / C)) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring

/-! ## Hoeffding's lemma (bounded centred random variable) -/

lemma hoeffding_range {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsProbabilityMeasure ν]
    {h : Y → ℝ} {L : ℝ} (hL : 0 ≤ L) (hm : Measurable h)
    (hbd : ∀ y y', |h y - h y'| ≤ L) (hmean : ∫ y, h y ∂ν = 0) (θ : ℝ) :
    ∫ y, Real.exp (θ * h y) ∂ν ≤ Real.exp (θ ^ 2 * L ^ 2 / 8) := by
  have hne : Nonempty Y := by
    rcases isEmpty_or_nonempty Y with hY | hY
    · exfalso
      have h1 := (inferInstance : IsProbabilityMeasure ν).measure_univ
      rw [Set.univ_eq_empty_iff.mpr hY] at h1
      simp at h1
    · exact hY
  obtain ⟨y₀⟩ := hne
  have hbdd : BddBelow (Set.range h) := by
    refine ⟨h y₀ - L, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := abs_le.mp (hbd y y₀)
    linarith
  have hbdu : BddAbove (Set.range h) := by
    refine ⟨h y₀ + L, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := abs_le.mp (hbd y y₀)
    linarith
  have hrne : (Set.range h).Nonempty := ⟨h y₀, Set.mem_range_self y₀⟩
  set a := sInf (Set.range h) with ha
  set b := sSup (Set.range h) with hb
  have hmem : ∀ y, h y ∈ Set.Icc a b := by
    intro y
    exact ⟨csInf_le hbdd ⟨y, rfl⟩, le_csSup hbdu ⟨y, rfl⟩⟩
  have hba : b - a ≤ L := by
    have hle : b ≤ a + L := by
      apply csSup_le hrne
      rintro _ ⟨y, rfl⟩
      have h1 : h y - L ≤ a := by
        apply le_csInf hrne
        rintro _ ⟨y', rfl⟩
        have := abs_le.mp (hbd y y')
        linarith
      linarith
    linarith
  have h1 : HasSubgaussianMGF h ((‖b - a‖₊ / 2) ^ 2) ν := by
    apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable
    · filter_upwards with y using hmem y
    · exact hmean
  have h2 := h1.mgf_le θ
  have h3 : ((‖b - a‖₊ / 2) ^ 2 : ℝ) ≤ L ^ 2 / 4 := by
    have h0 : (0:ℝ) ≤ b - a := by
      have := (hmem y₀).1.trans (hmem y₀).2; linarith
    have hnorm : (‖b - a‖₊ : ℝ) = b - a := by
      simp [Real.nnnorm_of_nonneg h0]
    rw [hnorm] at *
    nlinarith
  calc ∫ y, Real.exp (θ * h y) ∂ν
      ≤ Real.exp (((‖b - a‖₊ / 2) ^ 2 : ℝ) * θ ^ 2 / 2) := h2
    _ ≤ Real.exp (θ ^ 2 * L ^ 2 / 8) := by
        apply Real.exp_le_exp.mpr
        nlinarith

lemma finset_hoeffding {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (h : ι → ℝ) (L : ℝ) (hL : 0 ≤ L) (hbd : ∀ y y', |h y - h y'| ≤ L)
    (hmean : ∑ y, h y = 0) (θ : ℝ) :
    ∑ y, Real.exp (θ * h y) ≤ (Fintype.card ι : ℝ) * Real.exp (θ ^ 2 * L ^ 2 / 8) := by
  rcases isEmpty_or_nonempty ι with hem | hne
  · have hc : Fintype.card ι = 0 := Fintype.card_eq_zero
    simp [hc]
  · have hcpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hne
    obtain ⟨y₀⟩ := hne
    have hc0 : Fintype.card ι ≠ 0 := Nat.pos_iff_ne_zero.mp hcpos
    have hctop : (Fintype.card ι : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    set ν : Measure ι := (Fintype.card ι : ℝ≥0∞)⁻¹ • Measure.count with hν
    haveI : IsProbabilityMeasure ν := by
      constructor
      rw [hν, Measure.smul_apply, smul_eq_mul]
      have hcnt : Measure.count (Set.univ : Set ι) = (Fintype.card ι : ℝ≥0∞) := by
        rw [← Finset.coe_univ, Measure.count_apply_finset, Finset.card_univ]
      rw [hcnt]
      exact ENNReal.inv_mul_cancel (by simp [hc0]) hctop
    have hnn : ∫ y, Real.exp (θ * h y) ∂ν
        = (Fintype.card ι : ℝ)⁻¹ * ∑ y, Real.exp (θ * h y) := by
      rw [hν, integral_smul_measure, integral_count, smul_eq_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
    have hmm : ∫ y, h y ∂ν = (Fintype.card ι : ℝ)⁻¹ * ∑ y, h y := by
      rw [hν, integral_smul_measure, integral_count, smul_eq_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
    have hmean' : ∫ y, h y ∂ν = 0 := by rw [hmm, hmean, mul_zero]
    have h1 := hoeffding_range (ν := ν) hL (measurable_of_finite h) hbd hmean' θ
    rw [hnn] at h1
    have hcard : (0:ℝ) < Fintype.card ι := by exact_mod_cast hcpos
    calc ∑ y, Real.exp (θ * h y)
        = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ y, Real.exp (θ * h y)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcard), one_mul]
      _ ≤ (Fintype.card ι : ℝ) * Real.exp (θ ^ 2 * L ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hcard)

/-! ## The permutation part: concentration over a uniform injection -/

def embSnocEquiv (N n : ℕ) :
    (Σ p : Fin n ↪ Fin N, {y : Fin N // y ∉ Set.range p}) ≃ (Fin (n + 1) ↪ Fin N) :=
  Equiv.ofBijective (fun x => Fin.Embedding.snoc x.1 x.2.2) ⟨by
    rintro ⟨p, ⟨y, hy⟩⟩ ⟨p', ⟨y', hy'⟩⟩ h
    simp only at h
    have hlast : y = y' := by
      have hh := congrArg (fun e => e (Fin.last n)) h
      simpa [Fin.Embedding.snoc_last] using hh
    have hinit : p = p' := by
      have hh := congrArg Fin.Embedding.init h
      simpa [Fin.Embedding.init_snoc] using hh
    subst hinit
    subst hlast
    rfl, by
    intro q
    refine ⟨⟨Fin.Embedding.init q, ⟨q (Fin.last n), ?_⟩⟩, ?_⟩
    · rintro ⟨i, hi⟩
      have h1 : q (Fin.last n) = q (Fin.castSucc i) := hi.symm
      have h2 : Fin.last n = Fin.castSucc i := q.injective h1
      have h3 : (Fin.last n).val = (Fin.castSucc i).val := congrArg Fin.val h2
      simp only [Fin.val_last, Fin.val_castSucc] at h3
      omega
    · apply Function.Embedding.ext
      intro i
      show Fin.snoc (Fin.init ⇑q) (q (Fin.last n)) i = ⇑q i
      exact congrFun (Fin.snoc_init_self (⇑q)) i⟩

@[simp] lemma embSnocEquiv_apply {N n : ℕ}
    (x : Σ p : Fin n ↪ Fin N, {y : Fin N // y ∉ Set.range p}) :
    embSnocEquiv N n x = Fin.Embedding.snoc x.1 x.2.2 := by
  show (Equiv.ofBijective (fun x => Fin.Embedding.snoc x.1 x.2.2) _) x =
    Fin.Embedding.snoc x.1 x.2.2
  exact Equiv.ofBijective_apply _ _ _

lemma card_fiber_last (N n : ℕ) (p : Fin n ↪ Fin N) :
    Fintype.card {y : Fin N // y ∉ Set.range p} = N - n := by
  have h : Fintype.card {y : Fin N // y ∈ Set.range p} = n := by
    have h1 := Fintype.card_range p
    rw [Fintype.card_fin] at h1
    exact h1
  rw [Fintype.card_subtype_compl (fun y : Fin N => y ∈ Set.range p), h]
  simp

lemma card_inj_succ (N n : ℕ) :
    Fintype.card (Fin (n + 1) ↪ Fin N) = Fintype.card (Fin n ↪ Fin N) * (N - n) := by
  rw [← Fintype.card_congr (embSnocEquiv N n), Fintype.card_sigma]
  rw [Finset.sum_congr rfl (fun p _ => card_fiber_last N n p)]
  simp [Finset.sum_const]

def fiberEquiv {N D : ℕ} (p : Fin D ↪ Fin N) (τ : Equiv.Perm (Fin N)) :
    {y : Fin N // y ∉ Set.range p} ≃ {y : Fin N // y ∉ Set.range (p.trans τ.toEmbedding)} where
  toFun y := ⟨τ y.1, by
    rintro ⟨i, hi⟩
    exact y.2 ⟨i, τ.injective (by simpa using hi)⟩⟩
  invFun y := ⟨τ.symm y.1, by
    rintro ⟨i, hi⟩
    exact y.2 ⟨i, by
      simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
      rw [hi]; simp⟩⟩
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

@[simp] lemma fiberEquiv_apply {N D : ℕ} (p : Fin D ↪ Fin N) (τ : Equiv.Perm (Fin N))
    (y : {y : Fin N // y ∉ Set.range p}) :
    ((fiberEquiv p τ y : {y : Fin N // y ∉ Set.range (p.trans τ.toEmbedding)}) : Fin N) =
      τ y.1 := rfl

lemma pi_part (N D : ℕ) (hDN : D ≤ N) (f : (Fin D ↪ Fin N) → ℝ) (L : ℝ) (hL : 0 ≤ L) (θ : ℝ)
    (hf : ∀ (π : Fin D ↪ Fin N) (a c : Fin N), |f (π.trans (Equiv.swap a c).toEmbedding) - f π| ≤ L) :
    (∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - (∑ π : Fin D ↪ Fin N, f π) / (Fintype.card (Fin D ↪ Fin N) : ℝ))))
      / (Fintype.card (Fin D ↪ Fin N) : ℝ) ≤ Real.exp (θ ^ 2 * (D : ℝ) * L ^ 2 / 8) := by
  suffices key : ∀ D, D ≤ N → ∀ (f : (Fin D ↪ Fin N) → ℝ) (L : ℝ), 0 ≤ L → ∀ θ,
      (∀ (π : Fin D ↪ Fin N) (a c : Fin N), |f (π.trans (Equiv.swap a c).toEmbedding) - f π| ≤ L) →
      (∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - (∑ π : Fin D ↪ Fin N, f π) / (Fintype.card (Fin D ↪ Fin N) : ℝ))))
        / (Fintype.card (Fin D ↪ Fin N) : ℝ) ≤ Real.exp (θ ^ 2 * (D : ℝ) * L ^ 2 / 8) from
    key D hDN f L hL θ hf
  intro D
  induction D with
  | zero =>
      intro _ f L hL θ hf
      haveI hsub : Subsingleton (Fin 0 ↪ Fin N) := ⟨fun a b => by ext i; exact i.elim0⟩
      have huniv : (Finset.univ : Finset (Fin 0 ↪ Fin N)) = {default} := by
        ext x; simp [Subsingleton.elim x default]
      have hc : Fintype.card (Fin 0 ↪ Fin N) = 1 := by
        rw [← Finset.card_univ, huniv, Finset.card_singleton]
      have hall : ∀ π : Fin 0 ↪ Fin N, f π = f default := fun π => by
        rw [Subsingleton.elim π default]
      have hsum : (∑ π : Fin 0 ↪ Fin N, f π) = f default := by
        rw [Finset.sum_congr rfl (fun π _ => hall π), Finset.sum_const, huniv,
          Finset.card_singleton, nsmul_eq_mul]
        norm_num
      rw [hsum, hc]
      simp only [Nat.cast_one, div_one, Nat.cast_zero, zero_mul, zero_div, Real.exp_zero]
      have hconst : ∀ π : Fin 0 ↪ Fin N, Real.exp (θ * (f π - f default)) = 1 := fun π => by
        rw [hall π, sub_self, mul_zero, Real.exp_zero]
      rw [Finset.sum_congr rfl (fun π _ => hconst π), Finset.sum_const, huniv,
        Finset.card_singleton, nsmul_eq_mul]
      norm_num
  | succ D ih =>
      intro hD f L hL θ hf
      have hDlt : D < N := hD
      have hDN' : D ≤ N := Nat.le_of_succ_le hD
      have hneD : Nonempty (Fin D ↪ Fin N) := ⟨⟨Fin.castLE hDN', Fin.castLE_injective hDN'⟩⟩
      set gp : (Fin D ↪ Fin N) → ℝ := fun p =>
        (∑ y : {y : Fin N // y ∉ Set.range p}, f (Fin.Embedding.snoc p y.2))
          / (Fintype.card {y : Fin N // y ∉ Set.range p} : ℝ) with hgp
      have hfiber : ∀ p : Fin D ↪ Fin N, Fintype.card {y : Fin N // y ∉ Set.range p} = N - D :=
        fun p => card_fiber_last N D p
      have hfiberpos : ∀ p : Fin D ↪ Fin N, 0 < Fintype.card {y : Fin N // y ∉ Set.range p} := by
        intro p; rw [hfiber p]; exact Nat.sub_pos_of_lt hDlt
      have hsumQ : (∑ q : Fin (D+1) ↪ Fin N, f q)
          = ∑ p : Fin D ↪ Fin N, ∑ y : {y : Fin N // y ∉ Set.range p}, f (Fin.Embedding.snoc p y.2) := by
        rw [Fintype.sum_equiv (embSnocEquiv N D).symm (fun q => f q)
          (fun x => f ((embSnocEquiv N D) x)) (fun q => by simp)]
        rw [Fintype.sum_sigma]
        simp only [embSnocEquiv_apply]
      have hcardQ : Fintype.card (Fin (D+1) ↪ Fin N) = Fintype.card (Fin D ↪ Fin N) * (N - D) :=
        card_inj_succ N D
      have hdenD : (Fintype.card (Fin D ↪ Fin N) : ℝ) ≠ 0 := by
        have h : 0 < Fintype.card (Fin D ↪ Fin N) := Fintype.card_pos_iff.mpr hneD
        exact_mod_cast Nat.pos_iff_ne_zero.mp h
      have hdenN : ((N - D : ℕ) : ℝ) ≠ 0 := by
        have h : 0 < N - D := Nat.sub_pos_of_lt hDlt
        exact_mod_cast Nat.pos_iff_ne_zero.mp h
      set Ef : ℝ := (∑ q : Fin (D+1) ↪ Fin N, f q) / (Fintype.card (Fin (D+1) ↪ Fin N) : ℝ) with hEf
      set Eg : ℝ := (∑ p : Fin D ↪ Fin N, gp p) / (Fintype.card (Fin D ↪ Fin N) : ℝ) with hEg
      have hEfEg : Ef = Eg := by
        have hsp : (∑ p : Fin D ↪ Fin N, gp p)
            = ((∑ p : Fin D ↪ Fin N, ∑ y : {y : Fin N // y ∉ Set.range p},
                f (Fin.Embedding.snoc p y.2)) : ℝ) / ((N - D : ℕ) : ℝ) := by
          rw [hgp]
          simp only [hfiber, Finset.sum_div]
        rw [hEf, hEg, hsumQ, hcardQ, hsp]
        push_cast
        field_simp
        try ring
      have hsnoc_trans : ∀ (p : Fin D ↪ Fin N) (y y' : {y : Fin N // y ∉ Set.range p}),
          (Fin.Embedding.snoc p y.2).trans (Equiv.swap y.1 y'.1).toEmbedding
            = Fin.Embedding.snoc p y'.2 := by
        intro p y y'
        apply Function.Embedding.ext
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.Embedding.snoc_last, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
        · intro j
          simp only [Fin.Embedding.snoc_castSucc, Function.Embedding.trans_apply,
            Equiv.coe_toEmbedding]
          rw [Equiv.swap_apply_def]
          have hy : p j ≠ y.1 := fun h => y.2 ⟨j, h⟩
          have hy' : p j ≠ y'.1 := fun h => y'.2 ⟨j, h⟩
          simp [hy, hy']
      have hgp_trans : ∀ (p : Fin D ↪ Fin N) (a c : Fin N),
          |gp (p.trans (Equiv.swap a c).toEmbedding) - gp p| ≤ L := by
        intro p a c
        set τ := Equiv.swap a c with hτ
        have hcardτ : Fintype.card {y : Fin N // y ∉ Set.range (p.trans τ.toEmbedding)}
            = Fintype.card {y : Fin N // y ∉ Set.range p} :=
          Fintype.card_congr (fiberEquiv p τ).symm
        have hsnoc' : ∀ y : {y : Fin N // y ∉ Set.range p},
            Fin.Embedding.snoc (p.trans τ.toEmbedding) (fiberEquiv p τ y).2
              = (Fin.Embedding.snoc p y.2).trans τ.toEmbedding := by
          intro y
          apply Function.Embedding.ext
          intro i
          refine Fin.lastCases ?_ ?_ i
          · simp [Fin.Embedding.snoc_last, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
          · intro j
            simp [Fin.Embedding.snoc_castSucc, Function.Embedding.trans_apply,
              Equiv.coe_toEmbedding]
        have hgpτ : gp (p.trans τ.toEmbedding)
            = (∑ y : {y : Fin N // y ∉ Set.range p},
                f ((Fin.Embedding.snoc p y.2).trans τ.toEmbedding))
              / (Fintype.card {y : Fin N // y ∉ Set.range p} : ℝ) := by
          rw [hgp]
          simp only
          rw [hcardτ]
          congr 1
          rw [← Equiv.sum_comp (fiberEquiv p τ)
            (fun z => f (Fin.Embedding.snoc (p.trans τ.toEmbedding) z.2))]
          apply Finset.sum_congr rfl
          intro y _
          rw [hsnoc' y]
        rw [hgpτ, hgp]
        simp only
        have hpos : (0:ℝ) < (Fintype.card {y : Fin N // y ∉ Set.range p} : ℝ) := by
          exact_mod_cast hfiberpos p
        rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_sub_comm]
        calc |(∑ y : {y : Fin N // y ∉ Set.range p}, f (Fin.Embedding.snoc p y.2))
              - (∑ y : {y : Fin N // y ∉ Set.range p},
                  f ((Fin.Embedding.snoc p y.2).trans τ.toEmbedding))|
            = |∑ y : {y : Fin N // y ∉ Set.range p},
                (f (Fin.Embedding.snoc p y.2)
                  - f ((Fin.Embedding.snoc p y.2).trans τ.toEmbedding))| := by
              rw [Finset.sum_sub_distrib]
          _ ≤ ∑ y : {y : Fin N // y ∉ Set.range p},
                |f (Fin.Embedding.snoc p y.2)
                  - f ((Fin.Embedding.snoc p y.2).trans τ.toEmbedding)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _y : {y : Fin N // y ∉ Set.range p}, L := by
              apply Finset.sum_le_sum
              intro y _
              rw [hτ, abs_sub_comm]
              exact hf (Fin.Embedding.snoc p y.2) a c
          _ = L * (Fintype.card {y : Fin N // y ∉ Set.range p} : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      have hmain : (∑ q : Fin (D+1) ↪ Fin N, Real.exp (θ * (f q - Ef)))
          = ∑ p : Fin D ↪ Fin N, Real.exp (θ * (gp p - Ef)) *
              (∑ y : {y : Fin N // y ∉ Set.range p},
                Real.exp (θ * (f (Fin.Embedding.snoc p y.2) - gp p))) := by
        rw [Fintype.sum_equiv (embSnocEquiv N D).symm (fun q => Real.exp (θ * (f q - Ef)))
          (fun x => Real.exp (θ * (f ((embSnocEquiv N D) x) - Ef))) (fun q => by simp)]
        rw [Fintype.sum_sigma]
        simp only [embSnocEquiv_apply]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [← Real.exp_add]
        congr 1
        ring
      have hfibbound : ∀ p : Fin D ↪ Fin N,
          (∑ y : {y : Fin N // y ∉ Set.range p},
            Real.exp (θ * (f (Fin.Embedding.snoc p y.2) - gp p)))
            ≤ (Fintype.card {y : Fin N // y ∉ Set.range p} : ℝ) * Real.exp (θ ^ 2 * L ^ 2 / 8) := by
        intro p
        apply finset_hoeffding _ L hL
        · intro y y'
          have h := hf (Fin.Embedding.snoc p y.2) y.1 y'.1
          rw [hsnoc_trans p y y'] at h
          have h2 : (f (Fin.Embedding.snoc p y.2) - gp p) - (f (Fin.Embedding.snoc p y'.2) - gp p)
              = f (Fin.Embedding.snoc p y.2) - f (Fin.Embedding.snoc p y'.2) := by ring
          rw [h2]
          simpa [abs_sub_comm] using h
        · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hgp]
          simp only
          have hc0 : ((Fintype.card {y : Fin N // y ∉ Set.range p} : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.pos_iff_ne_zero.mp (hfiberpos p)
          field_simp
          ring
      have hIH := ih hDN' gp L hL θ hgp_trans
      have hIH' : (∑ p : Fin D ↪ Fin N, Real.exp (θ * (gp p - Ef))) / (Fintype.card (Fin D ↪ Fin N) : ℝ)
          ≤ Real.exp (θ ^ 2 * (D : ℝ) * L ^ 2 / 8) := by
        rw [hEfEg]
        exact hIH
      calc (∑ q : Fin (D+1) ↪ Fin N, Real.exp (θ * (f q - Ef))) / (Fintype.card (Fin (D+1) ↪ Fin N) : ℝ)
          = (∑ p : Fin D ↪ Fin N, Real.exp (θ * (gp p - Ef)) *
              (∑ y : {y : Fin N // y ∉ Set.range p},
                Real.exp (θ * (f (Fin.Embedding.snoc p y.2) - gp p))))
              / ((Fintype.card (Fin D ↪ Fin N) : ℝ) * ((N - D : ℕ) : ℝ)) := by
              rw [hmain, hcardQ]; push_cast; ring
        _ ≤ (∑ p : Fin D ↪ Fin N, Real.exp (θ * (gp p - Ef)) *
              (((Fintype.card {y : Fin N // y ∉ Set.range p} : ℕ) : ℝ) *
                Real.exp (θ ^ 2 * L ^ 2 / 8)))
              / ((Fintype.card (Fin D ↪ Fin N) : ℝ) * ((N - D : ℕ) : ℝ)) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              apply Finset.sum_le_sum
              intro p _
              exact mul_le_mul_of_nonneg_left (hfibbound p) (Real.exp_pos _).le
        _ = Real.exp (θ ^ 2 * L ^ 2 / 8) *
              ((∑ p : Fin D ↪ Fin N, Real.exp (θ * (gp p - Ef))) /
                (Fintype.card (Fin D ↪ Fin N) : ℝ)) := by
              have hc : ∀ p : Fin D ↪ Fin N,
                  ((Fintype.card {y : Fin N // y ∉ Set.range p} : ℕ) : ℝ) = ((N - D : ℕ) : ℝ) := by
                intro p; rw [hfiber p]
              simp only [hc]
              rw [← Finset.sum_mul]
              field_simp
              try ring
        _ ≤ Real.exp (θ ^ 2 * L ^ 2 / 8) * Real.exp (θ ^ 2 * (D : ℝ) * L ^ 2 / 8) := by
              exact mul_le_mul_of_nonneg_left hIH' (Real.exp_pos _).le
        _ = Real.exp (θ ^ 2 * ((D+1 : ℕ) : ℝ) * L ^ 2 / 8) := by
              rw [← Real.exp_add]; congr 1; push_cast; ring

/-! ## The coordinate decomposition -/

def prodFinZeroEquiv (β Rand : Type) : β × (Fin 0 → Rand) ≃ β where
  toFun p := p.1
  invFun x := (x, fun i => i.elim0)
  left_inv p := by
    obtain ⟨x, f⟩ := p
    simp only
    congr 1
    funext i
    exact i.elim0
  right_inv x := rfl

@[simp] lemma prodFinZeroEquiv_symm_apply (β Rand : Type) (x : β) :
    (prodFinZeroEquiv β Rand).symm x = (x, fun i => i.elim0) := rfl

def snocFun {Rand : Type} {b : ℕ} (R : Fin b → Rand) (r : Rand) : Fin (b + 1) → Rand :=
  Fin.snoc R r

@[simp] lemma snocFun_castSucc {Rand : Type} {b : ℕ} (R : Fin b → Rand) (r : Rand) (i : Fin b) :
    snocFun R r i.castSucc = R i := Fin.snoc_castSucc (α := fun _ => Rand) r R i

@[simp] lemma snocFun_last {Rand : Type} {b : ℕ} (R : Fin b → Rand) (r : Rand) :
    snocFun R r (Fin.last b) = r := Fin.snoc_last (α := fun _ => Rand) r R

@[simp] lemma snocFun_init {Rand : Type} {b : ℕ} (R : Fin b → Rand) (r : Rand) :
    Fin.init (snocFun R r) = R := Fin.init_snoc (α := fun _ => Rand) r R

def snocEquiv (Rand : Type) (b : ℕ) : ((Fin b → Rand) × Rand) ≃ (Fin (b + 1) → Rand) where
  toFun p := Fin.snoc p.1 p.2
  invFun R := (Fin.init R, R (Fin.last b))
  left_inv p := by
    obtain ⟨f, r⟩ := p
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv R := by
    simp only
    exact Fin.snoc_init_self R

@[simp] lemma snocEquiv_apply (Rand : Type) (b : ℕ) (p : (Fin b → Rand) × Rand) :
    snocEquiv Rand b p = Fin.snoc p.1 p.2 := rfl

@[simp] lemma snocEquiv_symm_apply (Rand : Type) (b : ℕ) (R : Fin (b + 1) → Rand) :
    (snocEquiv Rand b).symm R = (Fin.init R, R (Fin.last b)) := rfl

lemma sum_fun_succ {Rand : Type} [Fintype Rand] (b : ℕ) (g : (Fin (b + 1) → Rand) → ℝ) :
    ∑ R, g R = ∑ Rinit : Fin b → Rand, ∑ r : Rand, g (snocFun Rinit r) := by
  rw [Fintype.sum_equiv (snocEquiv Rand b).symm g
    (fun p : (Fin b → Rand) × Rand => g (snocFun p.1 p.2)) (fun R => by simp [snocFun])]
  rw [Fintype.sum_prod_type]

lemma card_fun_fin_succ {Rand : Type} [Fintype Rand] (b : ℕ) :
    Fintype.card (Fin (b + 1) → Rand) = Fintype.card (Fin b → Rand) * Fintype.card Rand := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_succ]

lemma snoc_congr {Rand : Type} {b : ℕ} {R R' : Fin b → Rand} {r : Rand} {i : Fin b}
    (h : ∀ i', i' ≠ i → R i' = R' i') :
    ∀ i' : Fin (b + 1), i' ≠ Fin.castSucc i → snocFun R r i' = snocFun R' r i' := by
  intro i' hi'
  rcases eq_or_ne i' (Fin.last b) with hlast | hlast
  · subst hlast; simp
  · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
    have hj : j ≠ i := fun hh => hi' (by rw [hh])
    simp [h j hj]


/-! ## Restricting permutations to an injection -/
def res {N d : ℕ} (e0 : Fin d ↪ Fin N) (π : Equiv.Perm (Fin N)) : Fin d ↪ Fin N := e0.trans π.toEmbedding

lemma res_apply {N d : ℕ} (e0 : Fin d ↪ Fin N) (π : Equiv.Perm (Fin N)) (x : Fin d) :
    res e0 π x = π (e0 x) := rfl

lemma res_eq_iff {N d : ℕ} (e0 : Fin d ↪ Fin N) (π : Equiv.Perm (Fin N)) (i : Fin d ↪ Fin N) :
    res e0 π = i ↔ ∀ x : Fin d, π (e0 x) = i x := by
  constructor
  · intro h x
    have := congrArg (fun f : Fin d ↪ Fin N => (f : Fin d → Fin N) x) h
    simpa [res] using this
  · intro h
    exact Function.Embedding.ext (fun x => by simpa [res] using h x)

lemma card_fibre_res {N d : ℕ} (e0 : Fin d ↪ Fin N) (i : Fin d ↪ Fin N) :
    Fintype.card {π : Equiv.Perm (Fin N) // res e0 π = i} = (N - d).factorial := by
  classical
  let ee : ↥(Set.range (⇑e0)) ≃ ↥(Set.range (⇑i)) :=
    (Equiv.ofInjective (⇑e0) e0.2).symm.trans (Equiv.ofInjective (⇑i) i.2)
  have hee_apply : ∀ y : Fin d,
      ee ⟨e0 y, Set.mem_range_self y⟩ = ⟨i y, Set.mem_range_self y⟩ := by
    intro y
    simp only [ee, Equiv.trans_apply, Equiv.ofInjective_apply, Equiv.ofInjective_symm_apply]
  have hiff : ∀ π : Equiv.Perm (Fin N),
      (res e0 π = i) ↔ ∀ x : ↥(Set.range (⇑e0)), (π : Fin N → Fin N) x = ee x := by
    intro π
    rw [res_eq_iff]
    constructor
    · intro h x
      obtain ⟨y, hy⟩ := x.2
      have hx : x = ⟨e0 y, Set.mem_range_self y⟩ := Subtype.ext hy.symm
      rw [hx, hee_apply y, h y]
    · intro h y
      have h1 := h ⟨e0 y, Set.mem_range_self y⟩
      rw [hee_apply y] at h1
      exact h1
  have hsub : Fintype.card {π : Equiv.Perm (Fin N) // res e0 π = i}
      = Fintype.card {π : Equiv.Perm (Fin N) //
          ∀ x : ↥(Set.range (⇑e0)), (π : Fin N → Fin N) x = ee x} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight hiff
  rw [hsub]
  have hcompl : Fintype.card {π : Equiv.Perm (Fin N) //
        ∀ x : ↥(Set.range (⇑e0)), (π : Fin N → Fin N) x = ee x}
      = Fintype.card (↥(Set.range (⇑e0))ᶜ ≃ ↥(Set.range (⇑i))ᶜ) :=
    Fintype.card_congr (Equiv.Set.compl ee)
  rw [hcompl]
  have hcs : Fintype.card ↥(Set.range (⇑e0)) = d := by
    have h := Fintype.card_congr (Equiv.ofInjective (⇑e0) e0.2)
    rw [Fintype.card_fin] at h
    exact h.symm
  have hds : Fintype.card ↥(Set.range (⇑i)) = d := by
    have h := Fintype.card_congr (Equiv.ofInjective (⇑i) i.2)
    rw [Fintype.card_fin] at h
    exact h.symm
  have hsc : Fintype.card (↥(Set.range (⇑e0))ᶜ) = N - d := by
    rw [Fintype.card_compl_set (Set.range (⇑e0)), Fintype.card_fin, hcs]
  have htc : Fintype.card (↥(Set.range (⇑i))ᶜ) = N - d := by
    rw [Fintype.card_compl_set (Set.range (⇑i)), Fintype.card_fin, hds]
  have hequiv : ↥(Set.range (⇑e0))ᶜ ≃ ↥(Set.range (⇑i))ᶜ :=
    Fintype.equivOfCardEq (by rw [hsc, htc])
  rw [Fintype.card_equiv hequiv, hsc]

lemma sum_perm_res {N d : ℕ} (e0 : Fin d ↪ Fin N) (H : (Fin d ↪ Fin N) → ℝ) :
    (∑ π : Equiv.Perm (Fin N), H (res e0 π)) = ((N - d).factorial : ℝ) * ∑ i, H i := by
  classical
  have hstep : (∑ π : Equiv.Perm (Fin N), H (res e0 π))
      = ∑ i : Fin d ↪ Fin N, ∑ π ∈ (univ.filter (fun π : Equiv.Perm (Fin N) => res e0 π = i)),
          H (res e0 π) := by
    rw [Finset.sum_fiberwise (s := (univ : Finset (Equiv.Perm (Fin N))))
      (g := fun π => res e0 π) (f := fun π => H (res e0 π))]
  rw [hstep]
  have hcf : ∀ i : Fin d ↪ Fin N,
      ((univ.filter (fun π : Equiv.Perm (Fin N) => res e0 π = i)).card : ℝ)
        = ((N - d).factorial : ℝ) := by
    intro i
    have h3 : (univ.filter (fun π : Equiv.Perm (Fin N) => res e0 π = i)).card
        = Fintype.card {π : Equiv.Perm (Fin N) // res e0 π = i} :=
      (Fintype.card_subtype _).symm
    rw [h3, card_fibre_res e0 i]
  have hinner : ∀ i : Fin d ↪ Fin N,
      (∑ π ∈ (univ.filter (fun π : Equiv.Perm (Fin N) => res e0 π = i)), H (res e0 π))
        = ((N - d).factorial : ℝ) * H i := by
    intro i
    rw [Finset.sum_congr rfl (fun π hp => by rw [(Finset.mem_filter.mp hp).2]),
      Finset.sum_const, nsmul_eq_mul, hcf i]
  rw [Finset.sum_congr rfl (fun i _ => hinner i), ← Finset.mul_sum]

lemma sum_perm_res_prod {N d : ℕ} {β : Type} [Fintype β] (e0 : Fin d ↪ Fin N)
    (R : (Fin d ↪ Fin N) → β → ℝ) :
    (∑ z : Equiv.Perm (Fin N) × β, R (e0.trans z.1.toEmbedding) z.2)
      = ((N - d).factorial : ℝ) * ∑ z : (Fin d ↪ Fin N) × β, R z.1 z.2 := by
  classical
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have h := sum_perm_res e0 (fun i => ∑ b : β, R i b)
  simp only [res] at h
  exact h

lemma expU_perm_res {N d : ℕ} (hdn : d ≤ N) {β : Type} [Fintype β] [Nonempty β]
    (e0 : Fin d ↪ Fin N) (G : (Fin d ↪ Fin N) → β → ℝ) :
    expU (fun z : Equiv.Perm (Fin N) × β => G (e0.trans z.1.toEmbedding) z.2)
      = expU (fun z : (Fin d ↪ Fin N) × β => G z.1 z.2) := by
  classical
  have hKpos : (0 : ℝ) < ((N - d).factorial : ℝ) := by
    have : 0 < (N - d).factorial := Nat.factorial_pos _
    exact_mod_cast this
  have hDpos : (0 : ℝ) < ((Fintype.card ((Fin d ↪ Fin N) × β) : ℕ) : ℝ) := by
    have hne : Nonempty ((Fin d ↪ Fin N) × β) :=
      ⟨(⟨Fin.castLE hdn, Fin.castLE_injective hdn⟩, Classical.arbitrary β)⟩
    have : 0 < Fintype.card ((Fin d ↪ Fin N) × β) := Fintype.card_pos_iff.mpr hne
    exact_mod_cast this
  have hcard : ((Fintype.card (Equiv.Perm (Fin N) × β) : ℕ) : ℝ)
      = ((N - d).factorial : ℝ) * ((Fintype.card ((Fin d ↪ Fin N) × β) : ℕ) : ℝ) := by
    have h := sum_perm_res_prod e0 (fun (_ : Fin d ↪ Fin N) (_ : β) => (1 : ℝ))
    simpa using h
  rw [expU, expU, sum_perm_res_prod e0 G, hcard]
  field_simp

lemma prU_perm_res {N d : ℕ} (hdn : d ≤ N) {β : Type} [Fintype β] [Nonempty β]
    (e0 : Fin d ↪ Fin N) (P : (Fin d ↪ Fin N) → β → Prop) :
    prU (fun z : Equiv.Perm (Fin N) × β => P (e0.trans z.1.toEmbedding) z.2)
      = prU (fun z : (Fin d ↪ Fin N) × β => P z.1 z.2) := by
  classical
  have hKpos : (0 : ℝ) < ((N - d).factorial : ℝ) := by
    have : 0 < (N - d).factorial := Nat.factorial_pos _
    exact_mod_cast this
  have hDpos : (0 : ℝ) < ((Fintype.card ((Fin d ↪ Fin N) × β) : ℕ) : ℝ) := by
    have hne : Nonempty ((Fin d ↪ Fin N) × β) :=
      ⟨(⟨Fin.castLE hdn, Fin.castLE_injective hdn⟩, Classical.arbitrary β)⟩
    have : 0 < Fintype.card ((Fin d ↪ Fin N) × β) := Fintype.card_pos_iff.mpr hne
    exact_mod_cast this
  have hcard : ((Fintype.card (Equiv.Perm (Fin N) × β) : ℕ) : ℝ)
      = ((N - d).factorial : ℝ) * ((Fintype.card ((Fin d ↪ Fin N) × β) : ℕ) : ℝ) := by
    have h := sum_perm_res_prod e0 (fun (_ : Fin d ↪ Fin N) (_ : β) => (1 : ℝ))
    simpa using h
  rw [prU_eq_sum, prU_eq_sum, hcard,
    sum_perm_res_prod e0 (fun i b => if P i b then (1 : ℝ) else 0)]
  field_simp

open Classical in
/-- Rewriting a filter over `Fin N` as a filter over `Fin d` along `e0`. -/
lemma filter_image_of_subset {N d : ℕ} {T : Finset ℕ} {e0 : Fin d ↪ Fin N}
    (he0 : ∀ a : Fin N, a ∈ Set.range (⇑e0) ↔ a.val ∈ T)
    {P : Fin N → Prop} (hP : ∀ i : Fin N, P i → i.val ∈ T) :
    (univ.filter P) = (univ.filter (fun t : Fin d => P (e0 t))).image e0 := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (he0 i).mpr (hP i h)
    exact ⟨t, by rw [ht]; exact h, ht⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht

/-! ## McDiarmid for a uniform injection times independent coordinates -/

theorem mgf_inj (N D : ℕ) (hDN : D ≤ N) (Rand : Type) [Fintype Rand] [Nonempty Rand] :
    ∀ (b : ℕ) (F : (Fin D ↪ Fin N) → (Fin b → Rand) → ℝ) (Lp Lr : ℝ), 0 ≤ Lp → 0 ≤ Lr →
    (∀ (π : Fin D ↪ Fin N) (R : Fin b → Rand) (a c : Fin N),
      |F (π.trans (Equiv.swap a c).toEmbedding) R - F π R| ≤ Lp) →
    (∀ (π : Fin D ↪ Fin N) (R R' : Fin b → Rand) (i : Fin b),
      (∀ i', i' ≠ i → R i' = R' i') → |F π R' - F π R| ≤ Lr) →
    ∀ θ : ℝ, 0 < θ →
      expU (fun z : (Fin D ↪ Fin N) × (Fin b → Rand) =>
        Real.exp (θ * (F z.1 z.2 - expU (fun z : (Fin D ↪ Fin N) × (Fin b → Rand) => F z.1 z.2))))
      ≤ Real.exp (θ ^ 2 * ((D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2) / 8) := by
  intro b
  induction b with
  | zero =>
      intro F Lp Lr hLp hLr hp hr θ hθ
      set f0 : (Fin D ↪ Fin N) → ℝ := fun π => F π (fun i => i.elim0) with hf0
      have hEF : expU (fun z : (Fin D ↪ Fin N) × (Fin 0 → Rand) => F z.1 z.2) = expU f0 := by
        rw [← expU_equiv (prodFinZeroEquiv (Fin D ↪ Fin N) Rand).symm
          (fun z : (Fin D ↪ Fin N) × (Fin 0 → Rand) => F z.1 z.2)]
        simp only [prodFinZeroEquiv_symm_apply, hf0]
      rw [hEF]
      rw [← expU_equiv (prodFinZeroEquiv (Fin D ↪ Fin N) Rand).symm
        (fun z : (Fin D ↪ Fin N) × (Fin 0 → Rand) =>
          Real.exp (θ * (F z.1 z.2 - expU f0)))]
      simp only [prodFinZeroEquiv_symm_apply, hf0]
      have h := pi_part N D hDN f0 Lp hLp θ (fun π a c => hp π (fun i => i.elim0) a c)
      rw [hf0] at h
      simpa [expU, Nat.cast_zero, zero_mul, add_zero, mul_assoc] using h
  | succ b ih =>
      intro F Lp Lr hLp hLr hp hr θ hθ
      haveI hneD : Nonempty (Fin D ↪ Fin N) := ⟨⟨Fin.castLE hDN, Fin.castLE_injective hDN⟩⟩
      haveI hneB : Nonempty (Fin b → Rand) := ⟨fun _ => Classical.arbitrary Rand⟩
      letI : MeasurableSpace Rand := ⊤
      haveI : MeasurableSingletonClass Rand := ⟨fun _ => trivial⟩
      have hcA : (0:ℝ) < (Fintype.card (Fin D ↪ Fin N) : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr hneD
      have hcB : (0:ℝ) < (Fintype.card (Fin b → Rand) : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr hneB
      have hcR : (0:ℝ) < (Fintype.card Rand : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty Rand)
      have hA0 : (Fintype.card (Fin D ↪ Fin N) : ℝ) ≠ 0 := ne_of_gt hcA
      have hB0 : (Fintype.card (Fin b → Rand) : ℝ) ≠ 0 := ne_of_gt hcB
      have hR0 : (Fintype.card Rand : ℝ) ≠ 0 := ne_of_gt hcR
      set EF : ℝ := expU (fun z : (Fin D ↪ Fin N) × (Fin (b+1) → Rand) => F z.1 z.2) with hEF
      set G : (Fin D ↪ Fin N) → (Fin b → Rand) → ℝ :=
        fun π R => (∑ r : Rand, F π (snocFun R r)) / (Fintype.card Rand : ℝ) with hG
      have hGmean : expU (fun z : (Fin D ↪ Fin N) × (Fin b → Rand) => G z.1 z.2) = EF := by
        have hc1 : (Fintype.card ((Fin D ↪ Fin N) × (Fin (b+1) → Rand)) : ℝ)
            = (Fintype.card ((Fin D ↪ Fin N) × (Fin b → Rand)) : ℝ) * (Fintype.card Rand : ℝ) := by
          rw [Fintype.card_prod, Fintype.card_prod, card_fun_fin_succ (Rand := Rand) b]
          push_cast
          ring
        have hL : (∑ x : Fin D ↪ Fin N, ∑ y : Fin b → Rand,
              (∑ r : Rand, F x (snocFun y r)) / (Fintype.card Rand : ℝ))
            = (∑ x : Fin D ↪ Fin N, ∑ y : Fin b → Rand, ∑ r : Rand, F x (snocFun y r))
              / (Fintype.card Rand : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_div]
        have hsum_all : (∑ z : (Fin D ↪ Fin N) × (Fin (b+1) → Rand), F z.1 z.2)
            = ∑ x : Fin D ↪ Fin N, ∑ y : Fin b → Rand, ∑ r : Rand, F x (snocFun y r) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro x _
          exact sum_fun_succ (Rand := Rand) b (fun y => F x y)
        rw [hEF, expU, expU, Fintype.sum_prod_type]
        simp only [hG]
        rw [hL, hc1, hsum_all]
        rw [div_div, mul_comm]
      have hpG : ∀ (π : Fin D ↪ Fin N) (R : Fin b → Rand) (a c : Fin N),
          |G (π.trans (Equiv.swap a c).toEmbedding) R - G π R| ≤ Lp := by
        intro π R a c
        simp only [hG]
        rw [← sub_div, abs_div, abs_of_pos hcR, div_le_iff₀ hcR]
        have hle : |(∑ r : Rand, F (π.trans (Equiv.swap a c).toEmbedding) (Fin.snoc R r))
              - (∑ r : Rand, F π (Fin.snoc R r))| ≤ ∑ _r : Rand, Lp := by
          rw [← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
          intro r _
          exact hp π (Fin.snoc R r) a c
        calc |(∑ r : Rand, F (π.trans (Equiv.swap a c).toEmbedding) (Fin.snoc R r))
              - (∑ r : Rand, F π (Fin.snoc R r))| ≤ ∑ _r : Rand, Lp := hle
          _ = Lp * (Fintype.card Rand : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      have hrG : ∀ (π : Fin D ↪ Fin N) (R R' : Fin b → Rand) (i : Fin b),
          (∀ i', i' ≠ i → R i' = R' i') → |G π R' - G π R| ≤ Lr := by
        intro π R R' i hi
        simp only [hG]
        rw [← sub_div, abs_div, abs_of_pos hcR, div_le_iff₀ hcR]
        have hkey : ∀ r : Rand, |F π (Fin.snoc R' r) - F π (Fin.snoc R r)| ≤ Lr := by
          intro r
          exact hr π (Fin.snoc R r) (Fin.snoc R' r) (Fin.castSucc i) (snoc_congr hi)
        calc |(∑ r : Rand, F π (Fin.snoc R' r)) - (∑ r : Rand, F π (Fin.snoc R r))|
            = |∑ r : Rand, (F π (Fin.snoc R' r) - F π (Fin.snoc R r))| := by
              rw [Finset.sum_sub_distrib]
          _ ≤ ∑ r : Rand, |F π (Fin.snoc R' r) - F π (Fin.snoc R r)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _r : Rand, Lr := Finset.sum_le_sum (fun r _ => hkey r)
          _ = Lr * (Fintype.card Rand : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      have hIH := ih G Lp Lr hLp hLr hpG hrG θ hθ
      have hfac : ∀ (π : Fin D ↪ Fin N) (R : Fin b → Rand),
          (∑ r : Rand, Real.exp (θ * (F π (snocFun R r) - EF)))
            = Real.exp (θ * (G π R - EF)) *
              (∑ r : Rand, Real.exp (θ * (F π (snocFun R r) - G π R))) := by
        intro π R
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [← Real.exp_add]
        congr 1
        simp only [hG]
        ring
      have hbound : ∀ (π : Fin D ↪ Fin N) (R : Fin b → Rand),
          (∑ r : Rand, Real.exp (θ * (F π (snocFun R r) - G π R)))
            ≤ (Fintype.card Rand : ℝ) * Real.exp (θ ^ 2 * Lr ^ 2 / 8) := by
        intro π R
        apply finset_hoeffding _ Lr hLr
        · intro r r'
          have h := hr π (snocFun R r) (snocFun R r') (Fin.last b) (by
            intro i' hi'
            obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi'
            simp)
          have h2 : (F π (snocFun R r) - G π R) - (F π (snocFun R r') - G π R)
              = F π (snocFun R r) - F π (snocFun R r') := by ring
          rw [h2]
          simpa [abs_sub_comm] using h
        · simp only [hG]
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
          ring
      have hstep1 : (∑ z : (Fin D ↪ Fin N) × (Fin (b+1) → Rand),
            Real.exp (θ * (F z.1 z.2 - EF)))
          = ∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, ∑ r : Rand,
              Real.exp (θ * (F π (snocFun R r) - EF)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro π _
        exact sum_fun_succ (Rand := Rand) b (fun R => Real.exp (θ * (F π R - EF)))
      have hstep2 : (∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, ∑ r : Rand,
              Real.exp (θ * (F π (snocFun R r) - EF)))
          = ∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)) *
              (∑ r : Rand, Real.exp (θ * (F π (snocFun R r) - G π R))) := by
        apply Finset.sum_congr rfl
        intro π _
        apply Finset.sum_congr rfl
        intro R _
        exact hfac π R
      have hstep3 : (∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)) *
              (∑ r : Rand, Real.exp (θ * (F π (snocFun R r) - G π R))))
          ≤ ∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)) *
              ((Fintype.card Rand : ℝ) * Real.exp (θ ^ 2 * Lr ^ 2 / 8)) := by
        apply Finset.sum_le_sum
        intro π _
        apply Finset.sum_le_sum
        intro R _
        exact mul_le_mul_of_nonneg_left (hbound π R) (Real.exp_pos _).le
      have hstep4 : (∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)) *
              ((Fintype.card Rand : ℝ) * Real.exp (θ ^ 2 * Lr ^ 2 / 8)))
            / ((Fintype.card (Fin D ↪ Fin N) : ℝ) *
               ((Fintype.card (Fin b → Rand) : ℝ) * (Fintype.card Rand : ℝ)))
          = Real.exp (θ ^ 2 * Lr ^ 2 / 8) *
              ((∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)))
                / ((Fintype.card (Fin D ↪ Fin N) : ℝ) * (Fintype.card (Fin b → Rand) : ℝ))) := by
        have h1 : ∀ π : Fin D ↪ Fin N,
            (∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)) *
              ((Fintype.card Rand : ℝ) * Real.exp (θ ^ 2 * Lr ^ 2 / 8)))
            = ((Fintype.card Rand : ℝ) * Real.exp (θ ^ 2 * Lr ^ 2 / 8)) *
              ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)) := by
          intro π
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro R _
          ring
        simp only [h1]
        rw [← Finset.mul_sum]
        field_simp
        try ring
      have hcard1 : (Fintype.card ((Fin D ↪ Fin N) × (Fin (b+1) → Rand)) : ℝ)
          = (Fintype.card (Fin D ↪ Fin N) : ℝ) *
            ((Fintype.card (Fin b → Rand) : ℝ) * (Fintype.card Rand : ℝ)) := by
        rw [Fintype.card_prod, card_fun_fin_succ (Rand := Rand) b]
        push_cast
        ring
      have hcard2 : (Fintype.card ((Fin D ↪ Fin N) × (Fin b → Rand)) : ℝ)
          = (Fintype.card (Fin D ↪ Fin N) : ℝ) * (Fintype.card (Fin b → Rand) : ℝ) := by
        rw [Fintype.card_prod]
        push_cast
        ring
      calc expU (fun z : (Fin D ↪ Fin N) × (Fin (b+1) → Rand) =>
              Real.exp (θ * (F z.1 z.2 - EF)))
          = (∑ z : (Fin D ↪ Fin N) × (Fin (b+1) → Rand), Real.exp (θ * (F z.1 z.2 - EF)))
              / ((Fintype.card (Fin D ↪ Fin N) : ℝ) *
                 ((Fintype.card (Fin b → Rand) : ℝ) * (Fintype.card Rand : ℝ))) := by
              rw [expU, hcard1]
        _ = (∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, ∑ r : Rand,
              Real.exp (θ * (F π (snocFun R r) - EF)))
              / ((Fintype.card (Fin D ↪ Fin N) : ℝ) *
                 ((Fintype.card (Fin b → Rand) : ℝ) * (Fintype.card Rand : ℝ))) := by
              rw [hstep1]
        _ = (∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)) *
              (∑ r : Rand, Real.exp (θ * (F π (snocFun R r) - G π R))))
              / ((Fintype.card (Fin D ↪ Fin N) : ℝ) *
                 ((Fintype.card (Fin b → Rand) : ℝ) * (Fintype.card Rand : ℝ))) := by
              rw [hstep2]
        _ ≤ (∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)) *
              ((Fintype.card Rand : ℝ) * Real.exp (θ ^ 2 * Lr ^ 2 / 8)))
              / ((Fintype.card (Fin D ↪ Fin N) : ℝ) *
                 ((Fintype.card (Fin b → Rand) : ℝ) * (Fintype.card Rand : ℝ))) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact hstep3
        _ = Real.exp (θ ^ 2 * Lr ^ 2 / 8) *
              ((∑ π : Fin D ↪ Fin N, ∑ R : Fin b → Rand, Real.exp (θ * (G π R - EF)))
                / ((Fintype.card (Fin D ↪ Fin N) : ℝ) * (Fintype.card (Fin b → Rand) : ℝ))) := hstep4
        _ = Real.exp (θ ^ 2 * Lr ^ 2 / 8) *
              expU (fun z : (Fin D ↪ Fin N) × (Fin b → Rand) =>
                Real.exp (θ * (G z.1 z.2 - EF))) := by
              rw [expU, Fintype.sum_prod_type, hcard2]
        _ ≤ Real.exp (θ ^ 2 * Lr ^ 2 / 8) * Real.exp (θ ^ 2 * ((D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2) / 8) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              simpa [hGmean] using hIH
        _ = Real.exp (θ ^ 2 * ((D : ℝ) * Lp ^ 2 + ((b+1 : ℕ) : ℝ) * Lr ^ 2) / 8) := by
              rw [← Real.exp_add]; congr 1; push_cast; ring

/-- The positions of row `j`: the `p` with `p * M + j < N`. -/
def rowPos (N M j : ℕ) : Finset ℕ := ((range N).filter (fun q => q % M = j)).image (fun q => q / M)

lemma mem_rowPos {N M j p : ℕ} (hM : 0 < M) (hj : j < M) :
    p ∈ rowPos N M j ↔ p * M + j < N := by
  classical
  simp only [rowPos, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨q, ⟨hqN, hqj⟩, rfl⟩
    have h : q / M * M + j = q := by rw [mul_comm (q / M) M, ← hqj, Nat.div_add_mod]
    rw [h]; exact hqN
  · intro h
    refine ⟨p * M + j, ⟨h, ?_⟩, ?_⟩
    · rw [mul_comm p M, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    · rw [mul_comm p M, Nat.mul_add_div hM, Nat.div_eq_of_lt hj, Nat.add_zero]

lemma mem_rowImage {N M : ℕ} (π : Equiv.Perm (Fin N)) {j : ℕ} {S : Finset ℕ} {p : ℕ} :
    p ∈ rowImage N M π j S ↔
      ∃ i : Fin N, i.val ∈ S ∧ (π i).val % M = j ∧ (π i).val / M = p := by
  classical
  unfold rowImage
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, h3⟩
    exact ⟨i, h1, h2, h3⟩
  · rintro ⟨i, h1, h2, h3⟩
    exact ⟨i, ⟨h1, h2⟩, h3⟩

lemma mem_assemble {N M : ℕ} (π : Equiv.Perm (Fin N)) (est : ℕ → Finset ℕ) (a : ℕ) :
    a ∈ assemble N M π est ↔
      ∃ i : Fin N, i.val = a ∧ (π i).val / M ∈ est ((π i).val % M) := by
  classical
  unfold assemble
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, h2, h1⟩
  · rintro ⟨i, h2, h1⟩
    exact ⟨i, h1, h2⟩

lemma rowImage_subset_rowPos {N M : ℕ} (π : Equiv.Perm (Fin N)) (hM : 0 < M) {j : ℕ} (hj : j < M)
    (S : Finset ℕ) : rowImage N M π j S ⊆ rowPos N M j := by
  classical
  intro p hp
  rw [mem_rowImage] at hp
  obtain ⟨i, -, hi, rfl⟩ := hp
  rw [mem_rowPos hM hj]
  have h : (π i).val / M * M + j = (π i).val := by
    rw [mul_comm ((π i).val / M) M, ← hi, Nat.div_add_mod]
  rw [h]; exact (π i).isLt

lemma card_rowImage {N M : ℕ} (π : Equiv.Perm (Fin N)) (hM : 0 < M) (S : Finset ℕ) (j : ℕ) :
    (rowImage N M π j S).card
      = (univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % M = j)).card := by
  classical
  rw [rowImage]
  rw [Finset.card_image_of_injOn]
  intro i hi i' hi' heq
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hi' heq
  have h1 : (π i).val = (π i').val := by
    rw [← Nat.div_add_mod (π i).val M, ← Nat.div_add_mod (π i').val M, heq, hi.2, hi'.2]
  exact π.injective (Fin.ext h1)

lemma sum_card_rowImage {N M : ℕ} (π : Equiv.Perm (Fin N)) (hM : 0 < M) (S : Finset ℕ) :
    ∑ j : Fin M, (rowImage N M π j.val S).card = (S ∩ range N).card := by
  classical
  have h1 : ∀ j : Fin M, (rowImage N M π j.val S).card
      = ((univ.filter (fun i : Fin N => i.val ∈ S)).filter
          (fun i => (⟨(π i).val % M, Nat.mod_lt _ hM⟩ : Fin M) = j)).card := by
    intro j
    rw [card_rowImage π hM S j.val]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := fun i : Fin N => (⟨(π i).val % M, Nat.mod_lt _ hM⟩ : Fin M))
    (s := univ.filter (fun i : Fin N => i.val ∈ S)) (t := univ) (fun i _ => Finset.mem_univ _)]
  have himg : (univ.filter (fun i : Fin N => i.val ∈ S)).image (fun i : Fin N => i.val)
      = S ∩ range N := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, h2⟩, h1, rfl⟩
  rw [← himg, Finset.card_image_of_injOn]
  intro i _ i' _ h
  exact Fin.ext h

/-- Counting a row's elements via the position map of a permutation. -/
lemma card_filter_mod_eq {N M : ℕ} (hM : 0 < M) (π : Equiv.Perm (Fin N)) (j : Fin M)
    (Q : ℕ → Prop) :
    (univ.filter (fun i : Fin N => (π i).val % M = j.val ∧ Q ((π i).val / M))).card
      = ((rowPos N M j.val).filter Q).card := by
  classical
  set s := univ.filter (fun i : Fin N => (π i).val % M = j.val ∧ Q ((π i).val / M)) with hs
  have hinj : Set.InjOn (fun i : Fin N => (π i).val / M) ↑s := by
    intro i hi i' hi' heq
    simp only [hs, Finset.coe_filter, Finset.mem_univ, true_and] at hi hi'
    have heq' : (π i).val / M = (π i').val / M := heq
    have h1 : (π i).val = (π i').val := by
      rw [← Nat.div_add_mod (π i).val M, ← Nat.div_add_mod (π i').val M, heq', hi.1, hi'.1]
    exact π.injective (Fin.ext h1)
  have himg : s.image (fun i : Fin N => (π i).val / M) = (rowPos N M j.val).filter Q := by
    ext p
    simp only [Finset.mem_image, hs, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_rowPos hM j.isLt]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, h2⟩
      have h : (π i).val / M * M + ↑j = (π i).val := by
        rw [mul_comm ((π i).val / M) M, ← h1, Nat.div_add_mod]
      rw [h]; exact (π i).isLt
    · rintro ⟨hp, hQ⟩
      refine ⟨π.symm ⟨p * M + j.val, hp⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [Equiv.apply_symm_apply]
        show (p * M + ↑j) % M = ↑j
        rw [mul_comm p M, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      · rw [Equiv.apply_symm_apply]
        show Q ((p * M + ↑j) / M)
        rw [show (p * M + ↑j) / M = p from by
          rw [mul_comm p M, Nat.mul_add_div hM, Nat.div_eq_of_lt j.isLt, Nat.add_zero]]
        exact hQ
      · rw [Equiv.apply_symm_apply]
        show (p * M + ↑j) / M = p
        rw [mul_comm p M, Nat.mul_add_div hM, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  rw [← himg, Finset.card_image_of_injOn hinj]

/-! ## Monotonicity of `prU` -/

lemma prU_mono {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a → Q a) : prU P ≤ prU Q := by
  rw [prU_eq_sum, prU_eq_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P a
  · rw [if_pos ha, if_pos (h a ha)]
  · rw [if_neg ha]
    split <;> norm_num

/-! ## Row images of an injection -/

/-- The row image in row `j` of `S`, computed from an injection `p` whose domain indexes the
relevant support `T` through the fixed injection `e0`. -/
def rowImageInj {N d : ℕ} (M : ℕ) (e0 p : Fin d ↪ Fin N) (S : Finset ℕ) (j : ℕ) : Finset ℕ :=
  (univ.filter (fun t : Fin d => (e0 t).val ∈ S ∧ (p t).val % M = j)).image (fun t => (p t).val / M)

lemma rowImageInj_swap {N M d : ℕ} (e0 p : Fin d ↪ Fin N) (S : Finset ℕ) (a c : Fin N) (j : ℕ)
    (hj1 : j ≠ a.val % M) (hj2 : j ≠ c.val % M) :
    rowImageInj M e0 (p.trans (Equiv.swap a c).toEmbedding) S j = rowImageInj M e0 p S j := by
  classical
  have hcomp : ∀ t : Fin d, (p.trans (Equiv.swap a c).toEmbedding) t = (Equiv.swap a c) (p t) :=
    fun t => rfl
  simp only [rowImageInj, hcomp]
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, hx⟩
    have hpt : p t ≠ a ∧ p t ≠ c := by
      constructor
      · intro h
        rw [h] at h2
        rw [Equiv.swap_apply_left] at h2
        exact hj2 h2.symm
      · intro h
        rw [h] at h2
        rw [Equiv.swap_apply_right] at h2
        exact hj1 h2.symm
    have h3 : (Equiv.swap a c) (p t) = p t := Equiv.swap_apply_of_ne_of_ne hpt.1 hpt.2
    rw [h3] at h2 hx
    exact ⟨t, ⟨h1, h2⟩, hx⟩
  · rintro ⟨t, ⟨h1, h2⟩, hx⟩
    have hpt : p t ≠ a ∧ p t ≠ c := by
      constructor
      · intro h; rw [h] at h2; exact hj1 h2.symm
      · intro h; rw [h] at h2; exact hj2 h2.symm
    have h3 : (Equiv.swap a c) (p t) = p t := Equiv.swap_apply_of_ne_of_ne hpt.1 hpt.2
    refine ⟨t, ⟨h1, ?_⟩, ?_⟩
    · rw [h3]; exact h2
    · rw [h3]; exact hx

/-- A sum's change under a modification that only touches the indices in `E`. -/
lemma abs_sum_sub_le {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ) (E : Finset ι) (C : ℝ)
    (h : ∀ i, i ∉ E → f i = g i) (hC : ∀ i, |f i - g i| ≤ C) :
    |∑ i, f i - ∑ i, g i| ≤ (E.card : ℝ) * C := by
  have h1 : (∑ i, f i - ∑ i, g i) = ∑ i ∈ E, (f i - g i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ E)]
    intro i _ hi
    simp [h i hi]
  rw [h1]
  calc |∑ i ∈ E, (f i - g i)| ≤ ∑ i ∈ E, |f i - g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ E, C := Finset.sum_le_sum (fun i _ => hC i)
    _ = (E.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Transferring uniform averages from permutations to injections -/

theorem tail_inj {N D b : ℕ} (hdn : D ≤ N) (Rand : Type) [Fintype Rand] [Nonempty Rand]
    (F : (Fin D ↪ Fin N) → (Fin b → Rand) → ℝ) (Lp Lr C Δ : ℝ)
    (hLp : 0 ≤ Lp) (hLr : 0 ≤ Lr)
    (hC : (D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2 ≤ C) (hCpos : 0 < C) (hΔ : 0 < Δ)
    (hp : ∀ (π : Fin D ↪ Fin N) (R : Fin b → Rand) (a c : Fin N),
      |F (π.trans (Equiv.swap a c).toEmbedding) R - F π R| ≤ Lp)
    (hr : ∀ (π : Fin D ↪ Fin N) (R R' : Fin b → Rand) (i : Fin b),
      (∀ i', i' ≠ i → R i' = R' i') → |F π R' - F π R| ≤ Lr) :
    prU (fun z : (Fin D ↪ Fin N) × (Fin b → Rand) =>
        expU (fun z' : (Fin D ↪ Fin N) × (Fin b → Rand) => F z'.1 z'.2) + Δ < F z.1 z.2)
      ≤ Real.exp (-(2 * Δ ^ 2 / C)) := by
  classical
  haveI hne : Nonempty (Fin D ↪ Fin N) := ⟨⟨Fin.castLE hdn, Fin.castLE_injective hdn⟩⟩
  set M0 : ℝ := expU (fun z : (Fin D ↪ Fin N) × (Fin b → Rand) => F z.1 z.2) with hM0
  have hmgf : ∀ θ : ℝ, 0 < θ →
      expU (fun z : (Fin D ↪ Fin N) × (Fin b → Rand) =>
        Real.exp (θ * (F z.1 z.2 - M0))) ≤ Real.exp (θ ^ 2 * C / 8) := by
    intro θ hθ
    have h1 := mgf_inj N D hdn Rand b F Lp Lr hLp hLr hp hr θ hθ
    rw [hM0]
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have h2 : 0 ≤ θ ^ 2 := sq_nonneg θ
    have h3 : θ ^ 2 * ((D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2) / 8 ≤ θ ^ 2 * C / 8 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hC h2
    linarith
  have hch := chernoff (fun z : (Fin D ↪ Fin N) × (Fin b → Rand) => F z.1 z.2 - M0) C hCpos hmgf hΔ
  refine (prU_mono ?_).trans hch
  intro z hz
  simp only [hM0] at hz ⊢
  linarith

/-! ## Lemma 4.2 (extended McDiarmid) applied to the placement of `J ∪ supp x`

Lemma 4.8 is Lemma 4.2 (`tail_inj`) applied to (i) the uniform placement `p` of `J ∪ supp x` and
(ii) the independent randomness of the `m` rows.  The lemmas in this section rewrite `U_s`, `V_s`
and `Z` as functions of `(p, R)` and bound their sensitivities, exactly as in the paper. -/

/-- A characteristic function only depends on the truth value. -/
lemma ind_eq_of_iff (P Q : Prop) [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1 : ℝ) else 0) = (if Q then (1 : ℝ) else 0) := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

lemma ind_abs_sub_le (P Q : Prop) [Decidable P] [Decidable Q] :
    |(if P then (1 : ℝ) else 0) - (if Q then (1 : ℝ) else 0)| ≤ 1 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- Membership in a symmetric difference. -/
lemma mem_symmDiff_iff {α : Type} [DecidableEq α] {s t : Finset α} {a : α} :
    a ∈ symmDiff s t ↔ (a ∈ s ∧ a ∉ t) ∨ (a ∈ t ∧ a ∉ s) := by
  classical
  simp only [symmDiff_def, Finset.sup_eq_union, Finset.mem_union, Finset.mem_sdiff]

/-- Membership in a row image computed from an injection (cf. `mem_rowImage`). -/
lemma mem_rowImageInj {N M d : ℕ} {e0 p : Fin d ↪ Fin N} {S : Finset ℕ} {j y : ℕ} :
    y ∈ rowImageInj M e0 p S j ↔
      ∃ t : Fin d, (e0 t).val ∈ S ∧ (p t).val % M = j ∧ (p t).val / M = y := by
  classical
  unfold rowImageInj
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    exact ⟨t, h1, h2, h3⟩
  · rintro ⟨t, h1, h2, h3⟩
    exact ⟨t, ⟨h1, h2⟩, h3⟩

/-- A row image depends on the placement `p = e0.trans π` only, not on the permutation itself. -/
lemma rowImage_eq_rowImageInj {N M d : ℕ} {T : Finset ℕ} {e0 : Fin d ↪ Fin N}
    (he0 : ∀ a : Fin N, a ∈ Set.range e0 ↔ a.val ∈ T) {π : Equiv.Perm (Fin N)}
    {S : Finset ℕ} (hS : S ⊆ T) (j : ℕ) :
    rowImage N M π j S = rowImageInj M e0 (e0.trans π.toEmbedding) S j := by
  classical
  ext y
  rw [mem_rowImage, mem_rowImageInj]
  constructor
  · rintro ⟨i, hiS, hj, hp⟩
    obtain ⟨t, ht⟩ := (he0 i).mpr (hS hiS)
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [ht]; exact hiS
    · rw [Function.Embedding.trans_apply, ht]; exact hj
    · rw [Function.Embedding.trans_apply, ht]; exact hp
  · rintro ⟨t, h1, h2, h3⟩
    exact ⟨e0 t, h1, h2, h3⟩

/-- The row image of a coordinate of the permutation, read at its own row. -/
lemma mem_rowImage_self {N M : ℕ} (hM : 0 < M) (π : Equiv.Perm (Fin N)) (S : Finset ℕ)
    (i : Fin N) : (π i).val / M ∈ rowImage N M π ((π i).val % M) S ↔ i.val ∈ S := by
  classical
  rw [mem_rowImage]
  constructor
  · rintro ⟨i', hi', hmod, hdiv⟩
    have h : (π i').val = (π i).val := by
      rw [← Nat.div_add_mod (π i').val M, ← Nat.div_add_mod (π i).val M, hmod, hdiv]
    have hii : i' = i := π.injective (Fin.ext h)
    rwa [hii] at hi'
  · intro hi
    exact ⟨i, hi, rfl, rfl⟩

/-- Membership in the assembled estimate, read at one coordinate. -/
lemma mem_assemble_iff {N M : ℕ} (π : Equiv.Perm (Fin N)) (est : ℕ → Finset ℕ) (i : Fin N) :
    i.val ∈ assemble N M π est ↔ (π i).val / M ∈ est ((π i).val % M) := by
  classical
  rw [mem_assemble]
  constructor
  · rintro ⟨i', hi', h⟩
    have hii : i' = i := Fin.ext hi'
    rwa [hii] at h
  · intro h
    exact ⟨i, rfl, h⟩

/-- The placement `e0` of a support `T ⊆ [N]` into `T.card` slots: the `i`-th smallest element. -/
lemma exists_range_emb {N : ℕ} (T : Finset ℕ) (hT : T ⊆ range N) :
    ∃ e0 : Fin T.card ↪ Fin N, ∀ a : Fin N, a ∈ Set.range e0 ↔ a.val ∈ T := by
  classical
  have hmem : ∀ t : Fin T.card, (T.orderEmbOfFin rfl : Fin T.card → ℕ) t ∈ T :=
    fun t => T.orderEmbOfFin_mem rfl t
  refine ⟨⟨fun t => ⟨T.orderEmbOfFin rfl t, Finset.mem_range.mp (hT (hmem t))⟩, ?_⟩, ?_⟩
  · intro t t' h
    refine (T.orderEmbOfFin rfl).injective ?_
    exact congrArg Fin.val h
  · intro a
    constructor
    · rintro ⟨t, rfl⟩
      exact hmem t
    · intro ha
      have h2 : a.val ∈ Set.range (T.orderEmbOfFin rfl : Fin T.card → ℕ) := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      obtain ⟨t, ht⟩ := h2
      exact ⟨t, Fin.ext ht⟩

/-- Counting a filter as a sum of indicators, over `ℝ`. -/
lemma card_filter_cast {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    ((univ.filter P).card : ℝ) = ∑ a, if P a then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_boole]

/-- `|s Δ t| = |s| + |t| - 2|s ∩ t|`. -/
lemma card_symmDiff_eq {α : Type} [DecidableEq α] (s t : Finset α) :
    (symmDiff s t).card = s.card + t.card - 2 * (s ∩ t).card := by
  classical
  have hd : Disjoint (s \ t) (t \ s) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have h1 : (symmDiff s t).card = (s \ t).card + (t \ s).card := by
    rw [symmDiff_def, Finset.sup_eq_union, Finset.card_union_of_disjoint hd]
  have h2 : (s \ t).card + (s ∩ t).card = s.card := Finset.card_sdiff_add_card_inter s t
  have h3 : (t \ s).card + (s ∩ t).card = t.card := by
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter t s
  have h4 : (s ∩ t).card ≤ s.card := by omega
  have h5 : (s ∩ t).card ≤ t.card := by omega
  omega

/-- `|s Δ t| = |s| + |t| - 2|s ∩ t|`, over `ℝ`. -/
lemma card_symmDiff_eq_real {α : Type} [DecidableEq α] (s t : Finset α) :
    ((symmDiff s t).card : ℝ) = (s.card : ℝ) + (t.card : ℝ) - 2 * ((s ∩ t).card : ℝ) := by
  have h := card_symmDiff_eq s t
  have h1 : (s ∩ t).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
  have h2 : (s ∩ t).card ≤ t.card := Finset.card_le_card Finset.inter_subset_right
  have hle : 2 * (s ∩ t).card ≤ s.card + t.card := by omega
  rw [h, Nat.cast_sub hle]
  push_cast
  ring

/-- Intersecting every row estimate with its row does not change the assembled set. -/
lemma assemble_inter_rowPos {N M : ℕ} (hM : 0 < M) (π : Equiv.Perm (Fin N))
    (est : ℕ → Finset ℕ) :
    assemble N M π (fun j => est j ∩ rowPos N M j) = assemble N M π est := by
  classical
  ext a
  rw [mem_assemble, mem_assemble]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, (Finset.mem_inter.mp h).1⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, Finset.mem_inter.mpr ⟨h, ?_⟩⟩
    rw [mem_rowPos hM (Nat.mod_lt _ hM), mul_comm (↑(π i) / M) M, Nat.div_add_mod]
    exact (π i).isLt

/-- The symmetric difference with the assembled estimate splits row by row.  This is the `Z`
decomposition `‖x Δ x̂‖₀ = Σ_j ‖S_j Δ Ŝ_j‖₀` of the paper: a coordinate belongs to the left side
iff its row-local image belongs to the right side of its own row, and the row map is a bijection
(`card_filter_mod_eq`). -/
lemma card_symmDiff_assemble {N M : ℕ} (hM : 0 < M) (π : Equiv.Perm (Fin N)) {x : Finset ℕ}
    (hx : x ⊆ range N) (est : ℕ → Finset ℕ) (hpos : ∀ j : Fin M, est j.val ⊆ rowPos N M j.val) :
    (symmDiff x (assemble N M π est)).card
      = ∑ j : Fin M, (symmDiff (rowImage N M π j.val x) (est j.val)).card := by
  classical
  set S : Finset ℕ := symmDiff x (assemble N M π est) with hS
  have hsub : S ⊆ range N := by
    intro a ha
    rw [hS] at ha
    rw [mem_symmDiff_iff] at ha
    rcases ha with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hx h1
    · obtain ⟨i, hi, -⟩ := (mem_assemble π est a).mp h1
      rw [← hi]
      exact Finset.mem_range.mpr i.isLt
  have hcast : S.card = (univ.filter (fun i : Fin N => i.val ∈ S)).card := by
    rw [← Finset.card_image_of_injOn (f := fun i : Fin N => i.val)
      (s := univ.filter (fun i : Fin N => i.val ∈ S))]
    · congr 1
      ext a
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ha
        exact ⟨⟨a, Finset.mem_range.mp (hsub ha)⟩, ha, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact hi
    · intro i _ i' _ h
      exact Fin.ext h
  have hfib : (univ.filter (fun i : Fin N => i.val ∈ S)).card
      = ∑ j : Fin M,
          ((univ.filter (fun i : Fin N => i.val ∈ S)).filter
            (fun i => (⟨(π i).val % M, Nat.mod_lt _ hM⟩ : Fin M) = j)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun i : Fin N => (⟨(π i).val % M, Nat.mod_lt _ hM⟩ : Fin M))
      (s := univ.filter (fun i : Fin N => i.val ∈ S))
      (t := (univ : Finset (Fin M))) (fun i _ => Finset.mem_univ _)]
  have hterm : ∀ j : Fin M,
      ((univ.filter (fun i : Fin N => i.val ∈ S)).filter
          (fun i => (⟨(π i).val % M, Nat.mod_lt _ hM⟩ : Fin M) = j)).card
        = (symmDiff (rowImage N M π j.val x) (est j.val)).card := by
    intro j
    have hsubrow : symmDiff (rowImage N M π j.val x) (est j.val) ⊆ rowPos N M j.val := by
      intro p hp
      rw [mem_symmDiff_iff] at hp
      rcases hp with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact rowImage_subset_rowPos π hM j.isLt x h1
      · exact hpos j h1
    refine Finset.card_bij (fun i _ => (π i).val / M) ?_ ?_ ?_
    · intro i hi
      have hi1 : i.val ∈ S := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      have hmod : (π i).val % M = j.val := congrArg Fin.val (Finset.mem_filter.mp hi).2
      have h1 : ((π i).val / M ∈ rowImage N M π j.val x) ↔ i.val ∈ x := by
        rw [← hmod]
        exact mem_rowImage_self hM π x i
      have h2 : ((π i).val / M ∈ est j.val) ↔ i.val ∈ assemble N M π est := by
        rw [mem_assemble_iff, hmod]
      rw [mem_symmDiff_iff, h1, h2]
      rw [hS, mem_symmDiff_iff] at hi1
      exact hi1
    · intro i hi i' hi' h
      have hji : (π i).val % M = j.val := congrArg Fin.val (Finset.mem_filter.mp hi).2
      have hji' : (π i').val % M = j.val := congrArg Fin.val (Finset.mem_filter.mp hi').2
      have hval : (π i).val = (π i').val := by
        rw [← Nat.div_add_mod (π i).val M, ← Nat.div_add_mod (π i').val M, h, hji, hji']
      exact π.injective (Fin.ext hval)
    · intro p hp
      have hprow : p ∈ rowPos N M j.val := hsubrow hp
      rw [mem_rowPos hM j.isLt] at hprow
      set i : Fin N := π.symm ⟨p * M + j.val, hprow⟩ with hi
      have hpi : π i = ⟨p * M + j.val, hprow⟩ := Equiv.apply_symm_apply π _
      have hdiv : (π i).val / M = p := by
        rw [hpi]
        show (p * M + j.val) / M = p
        rw [mul_comm p M, Nat.mul_add_div hM, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      have hmod : (π i).val % M = j.val := by
        rw [hpi]
        show (p * M + j.val) % M = j.val
        rw [mul_comm p M, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      refine ⟨i, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · have h1 : (p ∈ rowImage N M π j.val x) ↔ i.val ∈ x := by
            rw [← hdiv, ← hmod]
            exact mem_rowImage_self hM π x i
          have h2 : (p ∈ est j.val) ↔ i.val ∈ assemble N M π est := by
            rw [mem_assemble_iff, hmod, hdiv]
          rw [hS, mem_symmDiff_iff]
          rw [mem_symmDiff_iff, h1, h2] at hp
          exact hp
        · refine Fin.ext ?_
          show (π i).val % M = j.val
          exact hmod
      · exact hdiv
  rw [hcast, hfib]
  exact Finset.sum_congr rfl fun j _ => hterm j

/-! ### `U_s`, `V_s`, `Z` as functions of the placement and the row coins -/

/-- The prediction `q_{j,s}` of Definition 4.7, as a function of the placement `p` of `J ∪ supp x`
and the row coins `R`. -/
def predInj (sch : RowScheme) {d : ℕ} (e0 : Fin d ↪ Fin sch.N) (x J : Finset ℕ)
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) (j : Fin sch.m) :
    Option (ZMod 2) :=
  sch.predict j (R j) (rowImageInj sch.m e0 p J j.val)
    (sch.truePrefix j (R j) (rowImageInj sch.m e0 p x j.val) s.val)

/-- `U_s` (the number of `⊥` predictions) as a function of the placement and the row coins. -/
def Uinj (sch : RowScheme) {d : ℕ} (e0 : Fin d ↪ Fin sch.N) (x J : Finset ℕ)
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) : ℝ :=
  ∑ j : Fin sch.m, if predInj sch e0 x J p R s j = none then (1 : ℝ) else 0

/-- `V_s` (the number of incorrect predictions) as a function of the placement and the row coins. -/
def Vinj (sch : RowScheme) {d : ℕ} (e0 : Fin d ↪ Fin sch.N) (x J : Finset ℕ)
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) : ℝ :=
  ∑ j : Fin sch.m, if (∃ b : ZMod 2, predInj sch e0 x J p R s j = some b ∧
      b ≠ sch.code j (R j) (rowImageInj sch.m e0 p x j.val) s) then (1 : ℝ) else 0

/-- The final row estimate `x̂_j` of the exact execution, as a function of the placement and the
row coins. -/
def rowEstInj (sch : RowScheme) {d : ℕ} (e0 : Fin d ↪ Fin sch.N) (x J : Finset ℕ)
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (j : Fin sch.m) : Finset ℕ :=
  sch.final j (R j) (rowImageInj sch.m e0 p J j.val)
    (sch.truePrefix j (R j) (rowImageInj sch.m e0 p x j.val) sch.ℓ)

/-- `Ŝ_j = supp(x̂_j)`, truncated to the row so that `|Ŝ_j| ≤ K` holds for *every* placement; for
the true placement it is the untruncated intersection (`estInj_true`). -/
def estInj (sch : RowScheme) {d : ℕ} (e0 : Fin d ↪ Fin sch.N) (x J : Finset ℕ) (K : ℕ)
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (j : Fin sch.m) : Finset ℕ :=
  if (rowEstInj sch e0 x J p R j ∩ rowPos sch.N sch.m j.val).card ≤ K
  then rowEstInj sch e0 x J p R j ∩ rowPos sch.N sch.m j.val else ∅

/-- Lemma 4.8's `Z`, in the paper's decomposition `‖x‖₀ + Σ_j (|Ŝ_j| − 2|S_j ∩ Ŝ_j|)`, as a
function of the placement and the row coins. -/
def Zinj (sch : RowScheme) {d : ℕ} (e0 : Fin d ↪ Fin sch.N) (x J : Finset ℕ) (K : ℕ)
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) : ℝ :=
  (x.card : ℝ) + ∑ j : Fin sch.m,
    (((estInj sch e0 x J K p R j).card : ℝ) -
      2 * ((rowImageInj sch.m e0 p x j.val ∩ estInj sch e0 x J K p R j).card : ℝ))

/-! ### Agreement of the two pictures -/

/-- The prediction only depends on the placement `p = e0.trans π`. -/
lemma predInj_eq {sch : RowScheme} {d : ℕ} {T : Finset ℕ} {e0 : Fin d ↪ Fin sch.N}
    (he0 : ∀ a : Fin sch.N, a ∈ Set.range e0 ↔ a.val ∈ T)
    {x J : Finset ℕ} (hx : x ⊆ T) (hJ : J ⊆ T) (π : Equiv.Perm (Fin sch.N))
    (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) (j : Fin sch.m) :
    sch.exactPred (π, R) x J s j = predInj sch e0 x J (e0.trans π.toEmbedding) R s j := by
  classical
  simp only [RowScheme.exactPred, RowScheme.rowOf, predInj]
  rw [rowImage_eq_rowImageInj (M := sch.m) (S := J) he0 hJ (j := j.val),
    rowImage_eq_rowImageInj (M := sch.m) (S := x) he0 hx (j := j.val)]

/-- `U_s` only depends on the placement `p = e0.trans π`. -/
lemma U_eq_Uinj {sch : RowScheme} {d : ℕ} {T : Finset ℕ} {e0 : Fin d ↪ Fin sch.N}
    (he0 : ∀ a : Fin sch.N, a ∈ Set.range e0 ↔ a.val ∈ T)
    {x J : Finset ℕ} (hx : x ⊆ T) (hJ : J ⊆ T) (π : Equiv.Perm (Fin sch.N))
    (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) :
    (sch.U (π, R) x J s : ℝ) = Uinj sch e0 x J (e0.trans π.toEmbedding) R s := by
  classical
  have hc : ∀ j : Fin sch.m, (sch.exactPred (π, R) x J s j = none)
      ↔ (predInj sch e0 x J (e0.trans π.toEmbedding) R s j = none) := by
    intro j
    rw [predInj_eq he0 hx hJ]
  have hU : (sch.U (π, R) x J s : ℝ)
      = ∑ j : Fin sch.m,
        (if sch.exactPred (π, R) x J s j = none then (1 : ℝ) else 0) :=
    card_filter_cast (fun j : Fin sch.m => sch.exactPred (π, R) x J s j = none)
  rw [hU]
  unfold Uinj
  apply Finset.sum_congr rfl
  intro j _
  exact ind_eq_of_iff _ _ (hc j)

/-- `V_s` only depends on the placement `p = e0.trans π`. -/
lemma V_eq_Vinj {sch : RowScheme} {d : ℕ} {T : Finset ℕ} {e0 : Fin d ↪ Fin sch.N}
    (he0 : ∀ a : Fin sch.N, a ∈ Set.range e0 ↔ a.val ∈ T)
    {x J : Finset ℕ} (hx : x ⊆ T) (hJ : J ⊆ T) (π : Equiv.Perm (Fin sch.N))
    (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) :
    (sch.V (π, R) x J s : ℝ) = Vinj sch e0 x J (e0.trans π.toEmbedding) R s := by
  classical
  have hrowx : ∀ j : Fin sch.m, sch.rowOf (π, R) x j
      = rowImageInj sch.m e0 (e0.trans π.toEmbedding) x j.val := by
    intro j
    simp only [RowScheme.rowOf]
    exact rowImage_eq_rowImageInj (M := sch.m) (S := x) he0 hx (j := j.val)
  have hc : ∀ j : Fin sch.m,
      (∃ b : ZMod 2, sch.exactPred (π, R) x J s j = some b ∧
        b ≠ sch.code j (R j) (sch.rowOf (π, R) x j) s)
      ↔ (∃ b : ZMod 2, predInj sch e0 x J (e0.trans π.toEmbedding) R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 (e0.trans π.toEmbedding) x j.val) s) := by
    intro j
    rw [predInj_eq he0 hx hJ, hrowx j]
  have hV : (sch.V (π, R) x J s : ℝ)
      = ∑ j : Fin sch.m,
        (if (∃ b : ZMod 2, sch.exactPred (π, R) x J s j = some b ∧
          b ≠ sch.code j (R j) (sch.rowOf (π, R) x j) s) then (1 : ℝ) else 0) :=
    card_filter_cast (fun j : Fin sch.m => ∃ b : ZMod 2, sch.exactPred (π, R) x J s j = some b ∧
      b ≠ sch.code j (R j) (sch.rowOf (π, R) x j) s)
  rw [hV]
  unfold Vinj
  apply Finset.sum_congr rfl
  intro j _
  exact ind_eq_of_iff _ _ (hc j)

/-- Each row term of `Z` lies in `[-K,K]` when `|Ŝ_j| ≤ K`. -/
lemma abs_rowTerm_le {A B : Finset ℕ} {K : ℕ} (hB : B.card ≤ K) :
    |(B.card : ℝ) - 2 * ((A ∩ B).card : ℝ)| ≤ (K : ℝ) := by
  have h1 : ((A ∩ B).card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have h2 : (0 : ℝ) ≤ ((A ∩ B).card : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have h4 : (B.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
  rw [abs_le]
  constructor <;> linarith

/-- The estimate of one row only depends on the placement and the row coins. -/
lemma estInj_eq {sch : RowScheme} {d : ℕ} {T : Finset ℕ} {e0 : Fin d ↪ Fin sch.N}
    (he0 : ∀ a : Fin sch.N, a ∈ Set.range e0 ↔ a.val ∈ T)
    {x J : Finset ℕ} (hx : x ⊆ T) (hJ : J ⊆ T)
    (π : Equiv.Perm (Fin sch.N)) (R : Fin sch.m → sch.Rand) (j : Fin sch.m) :
    rowEstInj sch e0 x J (e0.trans π.toEmbedding) R j = sch.exactRowEst (π, R) x J j := by
  classical
  simp only [rowEstInj, RowScheme.exactRowEst, RowScheme.rowOf]
  rw [rowImage_eq_rowImageInj (M := sch.m) (S := J) he0 hJ (j := j.val),
    rowImage_eq_rowImageInj (M := sch.m) (S := x) he0 hx (j := j.val)]

/-- The truncation does not change the value at the true placement. -/
lemma estInj_true {sch : RowScheme} {d : ℕ} {T : Finset ℕ} {e0 : Fin d ↪ Fin sch.N}
    (he0 : ∀ a : Fin sch.N, a ∈ Set.range e0 ↔ a.val ∈ T)
    {x J : Finset ℕ} (hx : x ⊆ T) (hJ : J ⊆ T) (K : ℕ)
    (hest : ∀ (lr : sch.LocalSeed) (j : Fin sch.m), (sch.exactRowEst lr x J j).card ≤ K)
    (π : Equiv.Perm (Fin sch.N)) (R : Fin sch.m → sch.Rand) (j : Fin sch.m) :
    estInj sch e0 x J K (e0.trans π.toEmbedding) R j
      = rowEstInj sch e0 x J (e0.trans π.toEmbedding) R j ∩ rowPos sch.N sch.m j.val := by
  classical
  have hle : (rowEstInj sch e0 x J (e0.trans π.toEmbedding) R j
      ∩ rowPos sch.N sch.m j.val).card ≤ K := by
    refine le_trans (Finset.card_le_card Finset.inter_subset_left) ?_
    rw [estInj_eq he0 hx hJ π R j]
    exact hest (π, R) j
  simp only [estInj]
  rw [if_pos hle]

lemma estInj_subset {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ} {K : ℕ}
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (j : Fin sch.m) :
    estInj sch e0 x J K p R j ⊆ rowPos sch.N sch.m j.val := by
  classical
  simp only [estInj]
  by_cases h : (rowEstInj sch e0 x J p R j ∩ rowPos sch.N sch.m j.val).card ≤ K
  · rw [if_pos h]
    exact Finset.inter_subset_right
  · rw [if_neg h]
    exact Finset.empty_subset _

lemma estInj_card_le {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ} {K : ℕ}
    (hK : 1 ≤ K) (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (j : Fin sch.m) :
    (estInj sch e0 x J K p R j).card ≤ K := by
  classical
  simp only [estInj]
  by_cases h : (rowEstInj sch e0 x J p R j ∩ rowPos sch.N sch.m j.val).card ≤ K
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    simp only [Finset.card_empty]
    omega

/-- Congruence of the truncated estimate. -/
lemma estInj_congr {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ} {K : ℕ}
    {p p' : Fin d ↪ Fin sch.N} {R : Fin sch.m → sch.Rand} {j : Fin sch.m}
    (h : rowEstInj sch e0 x J p' R j = rowEstInj sch e0 x J p R j) :
    estInj sch e0 x J K p' R j = estInj sch e0 x J K p R j := by
  classical
  simp only [estInj, h]

/-- Congruence of the row estimate. -/
lemma rowEstInj_congr {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ}
    {p p' : Fin d ↪ Fin sch.N} {R : Fin sch.m → sch.Rand} {j : Fin sch.m}
    (hJ : rowImageInj sch.m e0 p' J j.val = rowImageInj sch.m e0 p J j.val)
    (hx : rowImageInj sch.m e0 p' x j.val = rowImageInj sch.m e0 p x j.val) :
    rowEstInj sch e0 x J p' R j = rowEstInj sch e0 x J p R j := by
  simp only [rowEstInj, hJ, hx]

/-! ### The final estimate `Z` and its decomposition `Z = ‖x‖₀ + Σ_j (|Ŝ_j| − 2|S_j ∩ Ŝ_j|)` -/

set_option maxHeartbeats 1000000 in
lemma Z_eq_Zinj {sch : RowScheme} {d : ℕ} {T : Finset ℕ} {e0 : Fin d ↪ Fin sch.N}
    (he0 : ∀ a : Fin sch.N, a ∈ Set.range e0 ↔ a.val ∈ T)
    {x J : Finset ℕ} (hx : x ⊆ T) (hJ : J ⊆ T) (hxn : x ⊆ range sch.N)
    (hm : 1 ≤ sch.m) (K : ℕ) (hK : 1 ≤ K)
    (hest : ∀ (lr : sch.LocalSeed) (j : Fin sch.m), (sch.exactRowEst lr x J j).card ≤ K)
    (π : Equiv.Perm (Fin sch.N)) (R : Fin sch.m → sch.Rand) :
    (sch.Z (π, R) x J : ℝ) = Zinj sch e0 x J K (e0.trans π.toEmbedding) R := by
  classical
  have hm0 : 0 < sch.m := by omega
  set est : ℕ → Finset ℕ :=
    fun i => if h : i < sch.m then estInj sch e0 x J K (e0.trans π.toEmbedding) R ⟨i, h⟩ else ∅
    with hestdef
  have hestval : ∀ j : Fin sch.m,
      est j.val = estInj sch e0 x J K (e0.trans π.toEmbedding) R j := by
    intro j
    simp only [hestdef, dif_pos j.isLt]
  set G : ℕ → Finset ℕ :=
    fun i => if h : i < sch.m then sch.exactRowEst (π, R) x J ⟨i, h⟩ else ∅ with hG
  have hA : sch.exactEstimate (π, R) x J = assemble sch.N sch.m π est := by
    have h1 : sch.exactEstimate (π, R) x J = assemble sch.N sch.m π G := by
      simp only [RowScheme.exactEstimate, RowScheme.assembled, RowScheme.exactRowEst, hG]
    rw [h1, ← assemble_inter_rowPos hm0 π G]
    congr 1
    funext i
    by_cases hi : i < sch.m
    · simp only [hG, dif_pos hi, hestdef, dif_pos hi]
      rw [estInj_true he0 hx hJ K hest π R ⟨i, hi⟩, estInj_eq he0 hx hJ π R ⟨i, hi⟩]
    · simp only [hG, dif_neg hi, hestdef, dif_neg hi, Finset.empty_inter]
  have hmain := card_symmDiff_assemble (N := sch.N) (M := sch.m) hm0 π hxn est
    (fun j => by
      rw [hestval j]
      exact estInj_subset (e0 := e0) (x := x) (J := J) (K := K) _ R j)
  have hZ1 : (sch.Z (π, R) x J : ℝ) = ((symmDiff x (assemble sch.N sch.m π est)).card : ℝ) := by
    rw [RowScheme.Z, hA]
  have hrowEq : ∀ j : Fin sch.m,
      symmDiff (rowImage sch.N sch.m π j.val x) (est j.val)
        = symmDiff (rowImageInj sch.m e0 (e0.trans π.toEmbedding) x j.val)
            (estInj sch e0 x J K (e0.trans π.toEmbedding) R j) := by
    intro j
    rw [hestval j,
      rowImage_eq_rowImageInj (M := sch.m) (S := x) he0 hx (j := j.val)]
  have hxcard : (x.card : ℝ)
      = ∑ j : Fin sch.m,
          ((rowImageInj sch.m e0 (e0.trans π.toEmbedding) x j.val).card : ℝ) := by
    have hnat : (x ∩ range sch.N).card = x.card := by rw [Finset.inter_eq_left.mpr hxn]
    have hcast : (x.card : ℝ)
        = ((∑ j : Fin sch.m, (rowImage sch.N sch.m π j.val x).card : ℕ) : ℝ) := by
      rw [← hnat, ← sum_card_rowImage π hm0 x]
    rw [hcast, Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [rowImage_eq_rowImageInj (M := sch.m) (S := x) he0 hx (j := j.val)]
  rw [hZ1, hmain]
  simp only [Zinj]
  rw [Nat.cast_sum, hxcard]
  simp only [hrowEq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [card_symmDiff_eq_real]
  ring

/-! ### Sensitivities: a position swap touches at most two rows, one row's coins one row -/

/-- Two functions on the rows that differ only off a set of at most two rows, by at most `C` each:
their sums differ by at most `2C`. -/
lemma abs_sum_sub_le_two {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ) {E : Finset ι}
    {C : ℝ} (hE : E.card ≤ 2) (h : ∀ i, i ∉ E → f i = g i) (hC : 0 ≤ C)
    (hbd : ∀ i, |f i - g i| ≤ C) :
    |∑ i, f i - ∑ i, g i| ≤ 2 * C := by
  have h1 := abs_sum_sub_le f g E C h hbd
  have h2 : ((E.card : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hE
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hC)

/-- Two functions on the rows that differ in a single row, by at most `C`: their sums differ by at
most `C`. -/
lemma abs_sum_sub_le_one {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ) {i₀ : ι}
    {C : ℝ} (h : ∀ i, i ≠ i₀ → f i = g i) (hC : 0 ≤ C) (hbd : ∀ i, |f i - g i| ≤ C) :
    |∑ i, f i - ∑ i, g i| ≤ C := by
  have h1 := abs_sum_sub_le f g {i₀} C (fun i hi => h i (by simpa using hi)) hbd
  have h2 : (({i₀} : Finset ι).card : ℝ) ≤ 1 := by simp
  simpa using h1.trans (mul_le_mul_of_nonneg_right h2 hC)

/-- The two rows hit by a placement swap. -/
lemma mem_two_rows {m : ℕ} (hm0 : 0 < m) (a c : ℕ) :
    ∃ E : Finset (Fin m), E.card ≤ 2 ∧ ∀ j : Fin m, j ∉ E → j.val ≠ a % m ∧ j.val ≠ c % m := by
  classical
  refine ⟨{⟨a % m, Nat.mod_lt _ hm0⟩, ⟨c % m, Nat.mod_lt _ hm0⟩}, ?_, ?_⟩
  · refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  · intro j hj
    have hj' : ¬(j = ⟨a % m, Nat.mod_lt _ hm0⟩ ∨ j = ⟨c % m, Nat.mod_lt _ hm0⟩) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
    rw [not_or] at hj'
    exact ⟨fun h => hj'.1 (Fin.ext h), fun h => hj'.2 (Fin.ext h)⟩

lemma predInj_swap_row {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ}
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) (a c : Fin sch.N)
    {j : Fin sch.m} (hj1 : j.val ≠ a.val % sch.m) (hj2 : j.val ≠ c.val % sch.m) :
    predInj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s j
      = predInj sch e0 x J p R s j := by
  classical
  simp only [predInj]
  rw [rowImageInj_swap e0 p J a c j.val hj1 hj2,
    rowImageInj_swap e0 p x a c j.val hj1 hj2]

lemma code_swap_row {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x : Finset ℕ}
    (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) (a c : Fin sch.N)
    {j : Fin sch.m} (hj1 : j.val ≠ a.val % sch.m) (hj2 : j.val ≠ c.val % sch.m) :
    sch.code j (R j) (rowImageInj sch.m e0 (p.trans (Equiv.swap a c).toEmbedding) x j.val) s
      = sch.code j (R j) (rowImageInj sch.m e0 p x j.val) s := by
  rw [rowImageInj_swap e0 p x a c j.val hj1 hj2]

/-- Lemma 4.8, `U_s`: a position swap affects at most two rows, changing the count by at most one
each, so `Lp = 2`. -/
lemma Uinj_swap {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ}
    (hm : 1 ≤ sch.m) (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ)
    (a c : Fin sch.N) :
    |Uinj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s - Uinj sch e0 x J p R s| ≤ 2 := by
  classical
  have hm0 : 0 < sch.m := by omega
  obtain ⟨E, hcard, hnot⟩ := mem_two_rows (m := sch.m) hm0 a.val c.val
  have hrow : ∀ j : Fin sch.m, j ∉ E →
      (if predInj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s j = none then (1:ℝ) else 0)
      = (if predInj sch e0 x J p R s j = none then (1:ℝ) else 0) := by
    intro j hj
    exact ind_eq_of_iff _ _ (by
      rw [predInj_swap_row p R s a c (hnot j hj).1 (hnot j hj).2])
  have hbd : ∀ j : Fin sch.m,
      |(if predInj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s j = none then (1:ℝ) else 0)
        - (if predInj sch e0 x J p R s j = none then (1:ℝ) else 0)| ≤ 1 :=
    fun j => ind_abs_sub_le _ _
  have h := abs_sum_sub_le_two
    (f := fun j : Fin sch.m =>
      if predInj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s j = none then (1:ℝ) else 0)
    (g := fun j : Fin sch.m => if predInj sch e0 x J p R s j = none then (1:ℝ) else 0)
    hcard hrow (by norm_num) hbd
  unfold Uinj
  simpa using h

/-- Lemma 4.8, `U_s`: replacing one row's randomness changes the count by at most one, so
`Lr = 1`. -/
lemma Uinj_coin {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ}
    (p : Fin d ↪ Fin sch.N) (R R' : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) (i : Fin sch.m)
    (hR : ∀ i', i' ≠ i → R i' = R' i') :
    |Uinj sch e0 x J p R' s - Uinj sch e0 x J p R s| ≤ 1 := by
  classical
  have hrow : ∀ j : Fin sch.m, j ≠ i →
      (if predInj sch e0 x J p R' s j = none then (1:ℝ) else 0)
      = (if predInj sch e0 x J p R s j = none then (1:ℝ) else 0) := by
    intro j hj
    exact ind_eq_of_iff _ _ (by simp only [predInj, hR j hj])
  have hbd : ∀ j : Fin sch.m,
      |(if predInj sch e0 x J p R' s j = none then (1:ℝ) else 0)
        - (if predInj sch e0 x J p R s j = none then (1:ℝ) else 0)| ≤ 1 :=
    fun j => ind_abs_sub_le _ _
  have h := abs_sum_sub_le_one
    (f := fun j : Fin sch.m => if predInj sch e0 x J p R' s j = none then (1:ℝ) else 0)
    (g := fun j : Fin sch.m => if predInj sch e0 x J p R s j = none then (1:ℝ) else 0)
    (i₀ := i) hrow (by norm_num) hbd
  unfold Uinj
  simpa using h

/-- Lemma 4.8, `V_s`: a position swap affects at most two rows, changing the count by at most one
each, so `Lp = 2`. -/
lemma Vinj_swap {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ}
    (hm : 1 ≤ sch.m) (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand) (s : Fin sch.ℓ)
    (a c : Fin sch.N) :
    |Vinj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s - Vinj sch e0 x J p R s| ≤ 2 := by
  classical
  have hm0 : 0 < sch.m := by omega
  obtain ⟨E, hcard, hnot⟩ := mem_two_rows (m := sch.m) hm0 a.val c.val
  have hrow : ∀ j : Fin sch.m, j ∉ E →
      (if (∃ b : ZMod 2, predInj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 (p.trans (Equiv.swap a c).toEmbedding) x j.val) s)
        then (1:ℝ) else 0)
      = (if (∃ b : ZMod 2, predInj sch e0 x J p R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0) := by
    intro j hj
    exact ind_eq_of_iff _ _ (by
      rw [predInj_swap_row p R s a c (hnot j hj).1 (hnot j hj).2,
        code_swap_row p R s a c (hnot j hj).1 (hnot j hj).2])
  have hbd : ∀ j : Fin sch.m,
      |(if (∃ b : ZMod 2, predInj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 (p.trans (Equiv.swap a c).toEmbedding) x j.val) s)
        then (1:ℝ) else 0)
        - (if (∃ b : ZMod 2, predInj sch e0 x J p R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0)| ≤ 1 :=
    fun j => ind_abs_sub_le _ _
  have h := abs_sum_sub_le_two
    (f := fun j : Fin sch.m =>
      if (∃ b : ZMod 2, predInj sch e0 x J (p.trans (Equiv.swap a c).toEmbedding) R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 (p.trans (Equiv.swap a c).toEmbedding) x j.val) s)
      then (1:ℝ) else 0)
    (g := fun j : Fin sch.m =>
      if (∃ b : ZMod 2, predInj sch e0 x J p R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0)
    hcard hrow (by norm_num) hbd
  unfold Vinj
  simpa using h

/-- Lemma 4.8, `V_s`: replacing one row's randomness changes the count by at most one, so
`Lr = 1`. -/
lemma Vinj_coin {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ}
    (p : Fin d ↪ Fin sch.N) (R R' : Fin sch.m → sch.Rand) (s : Fin sch.ℓ) (i : Fin sch.m)
    (hR : ∀ i', i' ≠ i → R i' = R' i') :
    |Vinj sch e0 x J p R' s - Vinj sch e0 x J p R s| ≤ 1 := by
  classical
  have hrow : ∀ j : Fin sch.m, j ≠ i →
      (if (∃ b : ZMod 2, predInj sch e0 x J p R' s j = some b ∧
        b ≠ sch.code j (R' j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0)
      = (if (∃ b : ZMod 2, predInj sch e0 x J p R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0) := by
    intro j hj
    exact ind_eq_of_iff _ _ (by simp only [predInj, hR j hj])
  have hbd : ∀ j : Fin sch.m,
      |(if (∃ b : ZMod 2, predInj sch e0 x J p R' s j = some b ∧
        b ≠ sch.code j (R' j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0)
        - (if (∃ b : ZMod 2, predInj sch e0 x J p R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0)| ≤ 1 :=
    fun j => ind_abs_sub_le _ _
  have h := abs_sum_sub_le_one
    (f := fun j : Fin sch.m =>
      if (∃ b : ZMod 2, predInj sch e0 x J p R' s j = some b ∧
        b ≠ sch.code j (R' j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0)
    (g := fun j : Fin sch.m =>
      if (∃ b : ZMod 2, predInj sch e0 x J p R s j = some b ∧
        b ≠ sch.code j (R j) (rowImageInj sch.m e0 p x j.val) s) then (1:ℝ) else 0)
    (i₀ := i) hrow (by norm_num) hbd
  unfold Vinj
  simpa using h

/-- Each row term of `Z` lies in `[-K,K]`, so two of them differ by at most `2K`. -/
lemma abs_rowTerm_sub_le {A A' B B' : Finset ℕ} {K : ℕ} (hB : B.card ≤ K) (hB' : B'.card ≤ K) :
    |((B.card : ℝ) - 2 * ((A ∩ B).card : ℝ))
        - ((B'.card : ℝ) - 2 * ((A' ∩ B').card : ℝ))| ≤ 2 * (K : ℝ) := by
  set X : ℝ := (B.card : ℝ) - 2 * ((A ∩ B).card : ℝ) with hX
  set Y : ℝ := (B'.card : ℝ) - 2 * ((A' ∩ B').card : ℝ) with hY
  have h1 : |X| ≤ (K : ℝ) := by rw [hX]; exact abs_rowTerm_le hB
  have h2 : |Y| ≤ (K : ℝ) := by rw [hY]; exact abs_rowTerm_le hB'
  calc |X - Y| = |X + (-Y)| := by rw [sub_eq_add_neg]
    _ ≤ |X| + |-Y| := abs_add_le _ _
    _ = |X| + |Y| := by rw [abs_neg]
    _ ≤ (K : ℝ) + (K : ℝ) := by linarith
    _ = 2 * (K : ℝ) := by ring

/-- The row estimate only depends on the coins of its own row. -/
lemma rowEstInj_apply_congr {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ}
    {p : Fin d ↪ Fin sch.N} {Q Q' : Fin sch.m → sch.Rand} {j : Fin sch.m} (h : Q j = Q' j) :
    rowEstInj sch e0 x J p Q j = rowEstInj sch e0 x J p Q' j := by
  simp only [rowEstInj, h]

/-- The (truncated) row estimate only depends on the coins of its own row. -/
lemma estInj_apply_congr {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ}
    {K : ℕ} {p : Fin d ↪ Fin sch.N} {Q Q' : Fin sch.m → sch.Rand} {j : Fin sch.m}
    (h : Q j = Q' j) :
    estInj sch e0 x J K p Q j = estInj sch e0 x J K p Q' j := by
  simp only [estInj]
  rw [rowEstInj_apply_congr h]

set_option maxHeartbeats 1000000 in
/-- Lemma 4.8, `Z`: a position swap affects at most two rows, and each summand of
`Z = ‖x‖₀ + Σ_j (|Ŝ_j| − 2|S_j ∩ Ŝ_j|)` lies in `[−K,K]`, so `Lp = 4K`. -/
lemma Zinj_swap {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ} {K : ℕ}
    (hm : 1 ≤ sch.m) (hK : 1 ≤ K) (p : Fin d ↪ Fin sch.N) (R : Fin sch.m → sch.Rand)
    (a c : Fin sch.N) :
    |Zinj sch e0 x J K (p.trans (Equiv.swap a c).toEmbedding) R - Zinj sch e0 x J K p R|
      ≤ 4 * (K : ℝ) := by
  classical
  have hm0 : 0 < sch.m := by omega
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
  obtain ⟨E, hcard, hnot⟩ := mem_two_rows (m := sch.m) hm0 a.val c.val
  set rowTerm : (Fin d ↪ Fin sch.N) → Fin sch.m → ℝ := fun q j =>
    ((estInj sch e0 x J K q R j).card : ℝ)
      - 2 * ((rowImageInj sch.m e0 q x j.val ∩ estInj sch e0 x J K q R j).card : ℝ)
    with hrowTerm
  have hZeq : ∀ q : Fin d ↪ Fin sch.N,
      Zinj sch e0 x J K q R = (x.card : ℝ) + ∑ j : Fin sch.m, rowTerm q j := fun q => rfl
  have hrow : ∀ j : Fin sch.m, j ∉ E →
      rowTerm (p.trans (Equiv.swap a c).toEmbedding) j = rowTerm p j := by
    intro j hj
    have h1 := (hnot j hj).1
    have h2 := (hnot j hj).2
    simp only [hrowTerm]
    rw [rowImageInj_swap e0 p x a c j.val h1 h2,
      estInj_congr (K := K) (rowEstInj_congr (rowImageInj_swap e0 p J a c j.val h1 h2)
        (rowImageInj_swap e0 p x a c j.val h1 h2))]
  have hbd : ∀ j : Fin sch.m,
      |rowTerm (p.trans (Equiv.swap a c).toEmbedding) j - rowTerm p j| ≤ 2 * (K : ℝ) := by
    intro j
    exact abs_rowTerm_sub_le (K := K)
      (estInj_card_le (e0 := e0) (x := x) (J := J) (K := K) hK
        (p.trans (Equiv.swap a c).toEmbedding) R j)
      (estInj_card_le (e0 := e0) (x := x) (J := J) (K := K) hK p R j)
  have hK2 : (0 : ℝ) ≤ 2 * (K : ℝ) := by positivity
  have h := abs_sum_sub_le_two (C := 2 * (K : ℝ))
    (f := rowTerm (p.trans (Equiv.swap a c).toEmbedding)) (g := rowTerm p) hcard hrow hK2 hbd
  rw [hZeq, hZeq]
  have hdiff : (x.card : ℝ) + ∑ j : Fin sch.m, rowTerm (p.trans (Equiv.swap a c).toEmbedding) j
      - ((x.card : ℝ) + ∑ j : Fin sch.m, rowTerm p j)
      = ∑ j : Fin sch.m, rowTerm (p.trans (Equiv.swap a c).toEmbedding) j
        - ∑ j : Fin sch.m, rowTerm p j := by ring
  rw [hdiff]
  calc |∑ j : Fin sch.m, rowTerm (p.trans (Equiv.swap a c).toEmbedding) j
        - ∑ j : Fin sch.m, rowTerm p j| ≤ 2 * (2 * (K : ℝ)) := h
    _ = 4 * (K : ℝ) := by ring

set_option maxHeartbeats 1000000 in
/-- Lemma 4.8, `Z`: replacing one row's randomness changes each summand by at most `2K`, so
`Lr = 2K`. -/
lemma Zinj_coin {sch : RowScheme} {d : ℕ} {e0 : Fin d ↪ Fin sch.N} {x J : Finset ℕ} {K : ℕ}
    (hK : 1 ≤ K) (p : Fin d ↪ Fin sch.N) (R R' : Fin sch.m → sch.Rand) (i : Fin sch.m)
    (hR : ∀ i', i' ≠ i → R i' = R' i') :
    |Zinj sch e0 x J K p R' - Zinj sch e0 x J K p R| ≤ 2 * (K : ℝ) := by
  classical
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
  set rowTerm : (Fin sch.m → sch.Rand) → Fin sch.m → ℝ := fun Q j =>
    ((estInj sch e0 x J K p Q j).card : ℝ)
      - 2 * ((rowImageInj sch.m e0 p x j.val ∩ estInj sch e0 x J K p Q j).card : ℝ)
    with hrowTerm
  have hZeq : ∀ Q : Fin sch.m → sch.Rand,
      Zinj sch e0 x J K p Q = (x.card : ℝ) + ∑ j : Fin sch.m, rowTerm Q j := fun Q => rfl
  have hrow : ∀ j : Fin sch.m, j ≠ i → rowTerm R' j = rowTerm R j := by
    intro j hj
    have h : R' j = R j := (hR j hj).symm
    simp only [hrowTerm]
    rw [estInj_apply_congr (x := x) (J := J) (K := K) (p := p) (Q := R') (Q' := R) (j := j) h]
  have hbd : ∀ j : Fin sch.m,
      |rowTerm R' j - rowTerm R j| ≤ 2 * (K : ℝ) := by
    intro j
    exact abs_rowTerm_sub_le (K := K)
      (estInj_card_le (e0 := e0) (x := x) (J := J) (K := K) hK p R' j)
      (estInj_card_le (e0 := e0) (x := x) (J := J) (K := K) hK p R j)
  have hK2 : (0 : ℝ) ≤ 2 * (K : ℝ) := by positivity
  have h := abs_sum_sub_le_one (C := 2 * (K : ℝ))
    (f := rowTerm R') (g := rowTerm R) (i₀ := i) hrow hK2 hbd
  rw [hZeq, hZeq]
  have hdiff : (x.card : ℝ) + ∑ j : Fin sch.m, rowTerm R' j
      - ((x.card : ℝ) + ∑ j : Fin sch.m, rowTerm R j)
      = ∑ j : Fin sch.m, rowTerm R' j - ∑ j : Fin sch.m, rowTerm R j := by ring
  rw [hdiff]
  exact h

/-! ### Transporting a uniform-injection bound back to the permutation law -/

lemma prU_congr {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) :
    prU P = prU Q := by
  classical
  rw [prU_eq_sum, prU_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => ind_eq_of_iff _ _ (h a)

/-! ## Lemma 4.8 (Concentration)

The concentration machinery above (`chernoff`, `hoeffding_range`, `finset_hoeffding`,
`embSnocEquiv`, `card_fiber_last`, `card_inj_succ`, `fiberEquiv`, `pi_part`, `sum_fun_succ`,
`snoc_congr`, `mgf_inj`, `tail_inj`) is fully proved.  What follows is the assembly of the target
statement from it, following the proof of Lemma 4.8 in `2609-version/4prob-tools.tex`:

* move to the uniform placement of `J ∪ supp(x)` into `|J ∪ supp(x)|` slots (`exists_range_emb`),
  transcribing `U_s`, `V_s`, `Z` (`U_eq_Uinj`, `V_eq_Vinj`, `Z_eq_Zinj`);
* a position swap affects at most two rows and changes `U_s`, `V_s` by at most one per row, so
  `Lp = 2` (`Uinj_swap`, `Vinj_swap`), and replacing one row's randomness changes each count by at
  most one, so `Lr = 1` (`Uinj_coin`, `Vinj_coin`); since `|J ∪ supp(x)| ≤ D` and `m ≤ D` the
  denominator is at most `4D + m ≤ 5D`;
* for `Z = ‖x‖₀ + Σ_j (|Ŝ_j| − 2|S_j ∩ Ŝ_j|)` each summand lies in `[−K,K]`, so a swap costs
  `4K` and one row's randomness `2K`, with denominator `16DK² + 4mK² ≤ 20DK²`
  (`Zinj_swap`, `Zinj_coin`);
* conclude with Lemma 4.2 in the form `tail_inj`, and transport back with `prU_perm_res`.

Deviation from the paper: the paper averages over the uniform permutation of `[N]`, we average over
the equivalent uniform injection of `|J ∪ supp(x)|` slots, using that every fibre of the restriction
map `res e0` has the same cardinality `(N-d)!` (`card_fibre_res`, `sum_perm_res`,
`expU_perm_res`, `prU_perm_res`).  This is the same argument, only with the irrelevant `(N-d)!`
factor cancelled once and for all. -/

set_option maxHeartbeats 1000000 in
/-- Lemma 4.8 (Concentration), PDF p.18 (printed p.17), for a node of any row scheme. -/
theorem lemma_4_8 (sch : RowScheme) (x J : Finset ℕ) (hx : x ⊆ range sch.N) (hJ : J ⊆ range sch.N)
    (hm : 1 ≤ sch.m) (D : ℕ) (hD : sch.m ≤ D) (hDJ : (J ∪ x).card ≤ D) (K : ℕ) (hK : 1 ≤ K)
    (hest : ∀ (lr : sch.LocalSeed) (j : Fin sch.m), (sch.exactRowEst lr x J j).card ≤ K)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    (∀ s : Fin sch.ℓ,
      prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.U lr' x J s : ℝ)) + Δ <
          (sch.U lr x J s : ℝ)) ≤ Real.exp (-(2 * Δ ^ 2 / (5 * (D : ℝ))))) ∧
    (∀ s : Fin sch.ℓ,
      prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.V lr' x J s : ℝ)) + Δ <
          (sch.V lr x J s : ℝ)) ≤ Real.exp (-(2 * Δ ^ 2 / (5 * (D : ℝ))))) ∧
    prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.Z lr' x J : ℝ)) + Δ <
        (sch.Z lr x J : ℝ)) ≤ Real.exp (-(Δ ^ 2 / (10 * (D : ℝ) * (K : ℝ) ^ 2))) := by
  classical
  have hm0 : 0 < sch.m := by omega
  have hTN : J ∪ x ⊆ range sch.N := Finset.union_subset hJ hx
  obtain ⟨e0, he0⟩ := exists_range_emb (J ∪ x) hTN
  have hxU : x ⊆ J ∪ x := Finset.subset_union_right
  have hJU : J ⊆ J ∪ x := Finset.subset_union_left
  have hdN : (J ∪ x).card ≤ sch.N := by
    have h := Finset.card_le_card hTN
    simpa using h
  have hdD : ((J ∪ x).card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDJ
  have hmD : (sch.m : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h1 : 1 ≤ D := le_trans hm hD
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hK)
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  refine ⟨?_, ?_, ?_⟩
  · -- `U_s`
    intro s
    have hG : ∀ z : sch.LocalSeed,
        (sch.U z x J s : ℝ) = Uinj sch e0 x J (res e0 z.1) z.2 s :=
      fun z => U_eq_Uinj he0 hxU hJU z.1 z.2 s
    have hinner : expU (fun lr' : sch.LocalSeed => (sch.U lr' x J s : ℝ))
        = expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
            Uinj sch e0 x J z'.1 z'.2 s) := by
      rw [show (fun lr' : sch.LocalSeed => (sch.U lr' x J s : ℝ))
          = (fun z : sch.LocalSeed => Uinj sch e0 x J (res e0 z.1) z.2 s) from funext hG]
      simp only [res]
      exact expU_perm_res hdN e0 (fun p R => Uinj sch e0 x J p R s)
    have hC : ((J ∪ x).card : ℝ) * 2 ^ 2 + (sch.m : ℝ) * 1 ^ 2 ≤ 5 * (D : ℝ) := by
      nlinarith [hdD, hmD]
    have hCpos : (0 : ℝ) < 5 * (D : ℝ) := by linarith
    calc prU (fun lr : sch.LocalSeed =>
            expU (fun lr' : sch.LocalSeed => (sch.U lr' x J s : ℝ)) + Δ < (sch.U lr x J s : ℝ))
        = prU (fun z : sch.LocalSeed =>
            expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
              Uinj sch e0 x J z'.1 z'.2 s) + Δ < Uinj sch e0 x J (res e0 z.1) z.2 s) := by
          apply prU_congr
          intro z
          rw [hinner, hG z]
      _ = prU (fun z : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
            expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
              Uinj sch e0 x J z'.1 z'.2 s) + Δ < Uinj sch e0 x J z.1 z.2 s) := by
          have h2 := prU_perm_res hdN e0
            (fun (p : Fin (J ∪ x).card ↪ Fin sch.N) (b : Fin sch.m → sch.Rand) =>
              expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
                Uinj sch e0 x J z'.1 z'.2 s) + Δ < Uinj sch e0 x J p b s)
          exact h2
      _ ≤ Real.exp (-(2 * Δ ^ 2 / (5 * (D : ℝ)))) :=
          tail_inj hdN sch.Rand (fun p R => Uinj sch e0 x J p R s) 2 1 (5 * (D : ℝ)) Δ
            (by norm_num) (by norm_num) hC hCpos hΔ
            (fun π R a c => Uinj_swap hm π R s a c)
            (fun π R R' i h => Uinj_coin π R R' s i h)
  · -- `V_s`
    intro s
    have hG : ∀ z : sch.LocalSeed,
        (sch.V z x J s : ℝ) = Vinj sch e0 x J (res e0 z.1) z.2 s :=
      fun z => V_eq_Vinj he0 hxU hJU z.1 z.2 s
    have hinner : expU (fun lr' : sch.LocalSeed => (sch.V lr' x J s : ℝ))
        = expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
            Vinj sch e0 x J z'.1 z'.2 s) := by
      rw [show (fun lr' : sch.LocalSeed => (sch.V lr' x J s : ℝ))
          = (fun z : sch.LocalSeed => Vinj sch e0 x J (res e0 z.1) z.2 s) from funext hG]
      simp only [res]
      exact expU_perm_res hdN e0 (fun p R => Vinj sch e0 x J p R s)
    have hC : ((J ∪ x).card : ℝ) * 2 ^ 2 + (sch.m : ℝ) * 1 ^ 2 ≤ 5 * (D : ℝ) := by
      nlinarith [hdD, hmD]
    have hCpos : (0 : ℝ) < 5 * (D : ℝ) := by linarith
    calc prU (fun lr : sch.LocalSeed =>
            expU (fun lr' : sch.LocalSeed => (sch.V lr' x J s : ℝ)) + Δ < (sch.V lr x J s : ℝ))
        = prU (fun z : sch.LocalSeed =>
            expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
              Vinj sch e0 x J z'.1 z'.2 s) + Δ < Vinj sch e0 x J (res e0 z.1) z.2 s) := by
          apply prU_congr
          intro z
          rw [hinner, hG z]
      _ = prU (fun z : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
            expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
              Vinj sch e0 x J z'.1 z'.2 s) + Δ < Vinj sch e0 x J z.1 z.2 s) := by
          have h2 := prU_perm_res hdN e0
            (fun (p : Fin (J ∪ x).card ↪ Fin sch.N) (b : Fin sch.m → sch.Rand) =>
              expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
                Vinj sch e0 x J z'.1 z'.2 s) + Δ < Vinj sch e0 x J p b s)
          exact h2
      _ ≤ Real.exp (-(2 * Δ ^ 2 / (5 * (D : ℝ)))) :=
          tail_inj hdN sch.Rand (fun p R => Vinj sch e0 x J p R s) 2 1 (5 * (D : ℝ)) Δ
            (by norm_num) (by norm_num) hC hCpos hΔ
            (fun π R a c => Vinj_swap hm π R s a c)
            (fun π R R' i h => Vinj_coin π R R' s i h)
  · -- `Z`
    have hG : ∀ z : sch.LocalSeed,
        (sch.Z z x J : ℝ) = Zinj sch e0 x J K (res e0 z.1) z.2 :=
      fun z => Z_eq_Zinj he0 hxU hJU hx hm K hK hest z.1 z.2
    have hinner : expU (fun lr' : sch.LocalSeed => (sch.Z lr' x J : ℝ))
        = expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
            Zinj sch e0 x J K z'.1 z'.2) := by
      rw [show (fun lr' : sch.LocalSeed => (sch.Z lr' x J : ℝ))
          = (fun z : sch.LocalSeed => Zinj sch e0 x J K (res e0 z.1) z.2) from funext hG]
      simp only [res]
      exact expU_perm_res hdN e0 (fun p R => Zinj sch e0 x J K p R)
    have hC : ((J ∪ x).card : ℝ) * (4 * (K : ℝ)) ^ 2 + (sch.m : ℝ) * (2 * (K : ℝ)) ^ 2
        ≤ 20 * (D : ℝ) * (K : ℝ) ^ 2 := by
      nlinarith [hdD, hmD, sq_nonneg (K : ℝ)]
    have hCpos : (0 : ℝ) < 20 * (D : ℝ) * (K : ℝ) ^ 2 := by positivity
    calc prU (fun lr : sch.LocalSeed =>
            expU (fun lr' : sch.LocalSeed => (sch.Z lr' x J : ℝ)) + Δ < (sch.Z lr x J : ℝ))
        = prU (fun z : sch.LocalSeed =>
            expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
              Zinj sch e0 x J K z'.1 z'.2) + Δ < Zinj sch e0 x J K (res e0 z.1) z.2) := by
          apply prU_congr
          intro z
          rw [hinner, hG z]
      _ = prU (fun z : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
            expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
              Zinj sch e0 x J K z'.1 z'.2) + Δ < Zinj sch e0 x J K z.1 z.2) := by
          have h2 := prU_perm_res hdN e0
            (fun (p : Fin (J ∪ x).card ↪ Fin sch.N) (b : Fin sch.m → sch.Rand) =>
              expU (fun z' : (Fin (J ∪ x).card ↪ Fin sch.N) × (Fin sch.m → sch.Rand) =>
                Zinj sch e0 x J K z'.1 z'.2) + Δ < Zinj sch e0 x J K p b)
          exact h2
      _ ≤ Real.exp (-(2 * Δ ^ 2 / (20 * (D : ℝ) * (K : ℝ) ^ 2))) :=
          tail_inj hdN sch.Rand (fun p R => Zinj sch e0 x J K p R) (4 * (K : ℝ)) (2 * (K : ℝ))
            (20 * (D : ℝ) * (K : ℝ) ^ 2) Δ
            (by positivity) (by positivity) hC hCpos hΔ
            (fun π R a c => Zinj_swap hm hK π R a c)
            (fun π R R' i h => Zinj_coin hK π R R' i h)
      _ = Real.exp (-(Δ ^ 2 / (10 * (D : ℝ) * (K : ℝ) ^ 2))) := by
          congr 1
          field_simp
          ring


end

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 4.8 (Concentration) - submission wrapper matching the target statement. -/
theorem solution (sch : RowScheme) (x J : Finset ℕ) (hx : x ⊆ range sch.N) (hJ : J ⊆ range sch.N)
    (hm : 1 ≤ sch.m) (D : ℕ) (hD : sch.m ≤ D) (hDJ : (J ∪ x).card ≤ D) (K : ℕ) (hK : 1 ≤ K)
    (hest : ∀ (lr : sch.LocalSeed) (j : Fin sch.m), (sch.exactRowEst lr x J j).card ≤ K)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    (∀ s : Fin sch.ℓ,
      prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.U lr' x J s : ℝ)) + Δ <
          (sch.U lr x J s : ℝ)) ≤ Real.exp (-(2 * Δ ^ 2 / (5 * (D : ℝ))))) ∧
    (∀ s : Fin sch.ℓ,
      prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.V lr' x J s : ℝ)) + Δ <
          (sch.V lr x J s : ℝ)) ≤ Real.exp (-(2 * Δ ^ 2 / (5 * (D : ℝ))))) ∧
    prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.Z lr' x J : ℝ)) + Δ <
        (sch.Z lr x J : ℝ)) ≤ Real.exp (-(Δ ^ 2 / (10 * (D : ℝ) * (K : ℝ) ^ 2))) :=
  LinearSetReconciliation327.Main.lemma_4_8 sch x J hx hJ hm D hD hDJ K hK hest Δ hΔ


