-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-15T13:58:37.34648+00:00
-- url     : https://prove2.me/submissions/8de27cd8-c911-4748-8ff0-ec9feb3cb9d2

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset
open MeasureTheory
open ProbabilityTheory

namespace LinearSetReconciliation327.Main

noncomputable section

open Classical in
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

open Classical in
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

open Classical in
def embSnocEquiv (N n : ℕ) :
    (Σ p : Fin n ↪ Fin N, {y : Fin N // y ∉ Set.range p}) ≃ (Fin (n + 1) ↪ Fin N) :=
  Equiv.ofBijective (fun x => Fin.Embedding.snoc x.1 x.2.2) ⟨by
    rintro ⟨p, ⟨y, hy⟩⟩ ⟨p', ⟨y', hy'⟩⟩ h
    have hlast : y = y' := by
      have := congrArg (fun e => e (Fin.last n)) h
      simpa [Fin.Embedding.snoc_last] using this
    have hinit : p = p' := by
      have := congrArg Fin.Embedding.init h
      simpa [Fin.Embedding.init_snoc] using this
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

@[simp] lemma embSnocEquiv_apply (N n : ℕ)
    (x : Σ p : Fin n ↪ Fin N, {y : Fin N // y ∉ Set.range p}) :
    embSnocEquiv N n x = Fin.Embedding.snoc x.1 x.2.2 := rfl

open Classical in
def fiberSwapEquiv (N n : ℕ) (p : Fin n ↪ Fin N) (τ : Equiv.Perm (Fin N)) :
    {y : Fin N // y ∉ Set.range p} ≃ {y : Fin N // y ∉ Set.range (p.trans τ.toEmbedding)} where
  toFun y := ⟨τ y.1, by
    rintro ⟨i, hi⟩
    exact y.2 ⟨i, τ.injective (by simpa using hi)⟩⟩
  invFun y := ⟨τ.symm y.1, by
    rintro ⟨i, hi⟩
    apply y.2
    refine ⟨i, ?_⟩
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    rw [hi]
    simp⟩
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

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
open Classical in
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
        Finset.card_singleton, nsmul_eq_mul, mul_one]
      simp
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
          Fin.Embedding.snoc p y'.2
            = (Fin.Embedding.snoc p y.2).trans (Equiv.swap y.1 y'.1).toEmbedding := by
        intro p y y'
        apply Function.Embedding.ext
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.Embedding.snoc_last]
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
          (Fintype.card_congr (fiberSwapEquiv N D p τ)).symm
        have hsnoc' : ∀ y : {y : Fin N // y ∉ Set.range p},
            Fin.Embedding.snoc (p.trans τ.toEmbedding) (fiberSwapEquiv N D p τ y).2
              = (Fin.Embedding.snoc p y.2).trans τ.toEmbedding := by
          intro y
          apply Function.Embedding.ext
          intro i
          refine Fin.lastCases ?_ ?_ i
          · simp only [Fin.Embedding.snoc_last, Function.Embedding.trans_apply,
              Equiv.coe_toEmbedding]
            rfl
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
          rw [← Equiv.sum_comp (fiberSwapEquiv N D p τ)
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
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [← Real.exp_add]
        simp only [embSnocEquiv_apply]
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
          rw [← hsnoc_trans p y y'] at h
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
        rw [hEfEg, hEg]
        exact hIH
      calc (∑ q : Fin (D+1) ↪ Fin N, Real.exp (θ * (f q - Ef))) / (Fintype.card (Fin (D+1) ↪ Fin N) : ℝ)
          = (∑ p : Fin D ↪ Fin N, Real.exp (θ * (gp p - Ef)) *
              (∑ y : {y : Fin N // y ∉ Set.range p},
                Real.exp (θ * (f (Fin.Embedding.snoc p y.2) - gp p))))
              / ((Fintype.card (Fin D ↪ Fin N) : ℝ) * ((N - D : ℕ) : ℝ)) := by
              rw [hmain, hcardQ]; push_cast
              simp only [embSnocEquiv_apply]
              try ring
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
              have hs : (∑ x : Fin D ↪ Fin N, Real.exp (θ * (gp x - Ef)) *
                    (↑(N - D) * Real.exp (θ ^ 2 * L ^ 2 / 8)))
                  = (∑ x : Fin D ↪ Fin N, Real.exp (θ * (gp x - Ef))) *
                    (↑(N - D) * Real.exp (θ ^ 2 * L ^ 2 / 8)) :=
                (Finset.sum_mul Finset.univ _ _).symm
              rw [hs]
              field_simp
              try ring
        _ ≤ Real.exp (θ ^ 2 * L ^ 2 / 8) * Real.exp (θ ^ 2 * (D : ℝ) * L ^ 2 / 8) := by
              exact mul_le_mul_of_nonneg_left hIH' (Real.exp_pos _).le
        _ = Real.exp (θ ^ 2 * ((D+1 : ℕ) : ℝ) * L ^ 2 / 8) := by
              rw [← Real.exp_add]; congr 1; push_cast; ring

lemma abs_sub_le_of_coord (Lr : ℝ) : ∀ (b : ℕ) (E : Fin b → Type) (g : (∀ i, E i) → ℝ)
    (R R0 : ∀ i, E i),
    (∀ (R R' : ∀ i, E i) (i : Fin b), (∀ i', i' ≠ i → R i' = R' i') → |g R' - g R| ≤ Lr) →
    |g R - g R0| ≤ b * Lr := by
  intro b
  induction b with
  | zero =>
      intro E g R R0 hr
      have h : R = R0 := funext fun i => Fin.elim0 i
      rw [h, sub_self, abs_zero]
      simp
  | succ b ih =>
      intro E g R R0 hr
      set m : ∀ i : Fin (b+1), E i := Fin.cons (R0 0) (fun j => R (Fin.succ j)) with hm
      have hRm : |g R - g m| ≤ Lr := by
        exact hr m R 0 (by
          intro i' hi'
          cases i' using Fin.cases with
          | zero => exact absurd rfl hi'
          | succ j => rfl)
      have hmidR0 : |g m - g R0| ≤ b * Lr := by
        have h := ih (fun j : Fin b => E (Fin.succ j)) (fun r => g (Fin.cons (R0 0) r))
          (fun j => R (Fin.succ j)) (fun j => R0 (Fin.succ j)) ?_
        · have hR0 : Fin.cons (R0 0) (fun j => R0 (Fin.succ j)) = R0 := Fin.cons_self_tail R0
          rwa [← hm, hR0] at h
        · intro r r' j hj
          apply hr (Fin.cons (R0 0) r) (Fin.cons (R0 0) r') (Fin.succ j)
          intro i' hi'
          cases i' using Fin.cases with
          | zero => rfl
          | succ k =>
              simp only [Fin.cons_succ]
              exact hj k (fun hkj => hi' (by rw [hkj]))
      have harg : g R - g R0 = (g R - g m) + (g m - g R0) := by ring
      calc |g R - g R0| = |(g R - g m) + (g m - g R0)| := by rw [harg]
        _ ≤ |g R - g m| + |g m - g R0| := abs_add_le _ _
        _ ≤ Lr + b * Lr := add_le_add hRm hmidR0
        _ = ((b + 1 : ℕ) : ℝ) * Lr := by push_cast; ring

lemma product_part :
    ∀ (b : ℕ) (E : Fin b → Type) [∀ i, MeasurableSpace (E i)]
      (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
      (Lr : ℝ) (hLr : 0 ≤ Lr) (g : (∀ i, E i) → ℝ) (hg : Measurable g),
      (∀ (R R' : ∀ i, E i) (i : Fin b), (∀ i', i' ≠ i → R i' = R' i') → |g R' - g R| ≤ Lr) →
      (∫ R, g R ∂Measure.pi μ) = 0 →
      ∀ θ : ℝ, ∫ R, Real.exp (θ * g R) ∂Measure.pi μ ≤ Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8) := by
  intro b
  induction b with
  | zero =>
      intro E _ μ _ Lr hLr g hg hr hmean θ
      obtain ⟨R0⟩ := nonempty_of_isProbabilityMeasure (Measure.pi μ)
      have hconst : ∀ R : ∀ i : Fin 0, E i, g R = g R0 := fun R => by
        rw [Subsingleton.elim R R0]
      have hint : ∫ R, g R ∂Measure.pi μ = g R0 := by
        rw [show (∫ R, g R ∂Measure.pi μ) = ∫ R, g R0 ∂Measure.pi μ from
          integral_congr_ae (Filter.Eventually.of_forall hconst)]
        simp
      have hg0 : g R0 = 0 := by rw [← hint]; exact hmean
      have hexp : ∀ R, Real.exp (θ * g R) = 1 := fun R => by
        rw [hconst R, hg0, mul_zero, Real.exp_zero]
      rw [show (∫ R, Real.exp (θ * g R) ∂Measure.pi μ) = ∫ R, (1:ℝ) ∂Measure.pi μ from
        integral_congr_ae (Filter.Eventually.of_forall hexp)]
      simp
  | succ b ih =>
      intro E _ μ _ Lr hLr g hg hr hmean θ
      haveI hne : ∀ i, Nonempty (E i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
      let R0 : ∀ i : Fin (b+1), E i := fun i => Classical.choice (hne i)
      set C : ℝ := |g R0| + ((b+1 : ℕ) : ℝ) * Lr with hC
      have hbdd : ∀ R, |g R| ≤ C := by
        intro R
        have h := abs_sub_le_of_coord Lr (b+1) E g R R0 hr
        have h2 : |g R| ≤ |g R0| + |g R - g R0| := by
          have harg : g R = g R0 + (g R - g R0) := by ring
          calc |g R| = |g R0 + (g R - g R0)| := by conv_lhs => rw [harg]
            _ ≤ |g R0| + |g R - g R0| := abs_add_le _ _
        rw [hC]
        linarith
      let E' : Fin b → Type := fun j => E (((0 : Fin (b+1)).succAbove j))
      let μ' : ∀ j : Fin b, Measure (E' j) := fun j => μ (((0 : Fin (b+1)).succAbove j))
      set e : (∀ i, E i) ≃ᵐ E 0 × (∀ j : Fin b, E (((0 : Fin (b+1)).succAbove j))) :=
        MeasurableEquiv.piFinSuccAbove E 0 with he_def
      have he : MeasurePreserving e (Measure.pi μ) ((μ 0).prod (Measure.pi μ')) := by
        rw [he_def]
        exact measurePreserving_piFinSuccAbove μ 0
      have e_symm : ∀ (x : E 0) (r : ∀ j, E' j), e.symm (x, r) = Fin.insertNth 0 x r := by
        intro x r
        rw [he_def, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rfl
      have hFmeas : Measurable (fun p : E 0 × (∀ j, E' j) => Real.exp (θ * g (e.symm p))) := by
        exact Real.measurable_exp.comp (measurable_const.mul (hg.comp e.symm.measurable))
      have hexp_bound : ∀ p : E 0 × (∀ j, E' j),
          Real.exp (θ * g (e.symm p)) ≤ Real.exp (|θ| * C) := by
        intro p
        apply Real.exp_le_exp.mpr
        calc θ * g (e.symm p) ≤ |θ * g (e.symm p)| := le_abs_self _
          _ = |θ| * |g (e.symm p)| := abs_mul θ _
          _ ≤ |θ| * C := mul_le_mul_of_nonneg_left (hbdd (e.symm p)) (abs_nonneg θ)
      have hFbdd : ∀ p : E 0 × (∀ j, E' j),
          ‖Real.exp (θ * g (e.symm p))‖ ≤ Real.exp (|θ| * C) := by
        intro p
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hexp_bound p
      have hFint : Integrable (fun p : E 0 × (∀ j, E' j) => Real.exp (θ * g (e.symm p)))
          ((μ 0).prod (Measure.pi μ')) :=
        Integrable.of_bound hFmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hFbdd)
      have h1 : ∫ R, Real.exp (θ * g R) ∂Measure.pi μ
          = ∫ p : E 0 × (∀ j, E' j), Real.exp (θ * g (e.symm p))
              ∂((μ 0).prod (Measure.pi μ')) := by
        rw [← he.symm.integral_comp']
      have h2 : ∫ p : E 0 × (∀ j, E' j), Real.exp (θ * g (e.symm p))
            ∂((μ 0).prod (Measure.pi μ'))
          = ∫ r, ∫ x, Real.exp (θ * g (e.symm (x, r))) ∂(μ 0) ∂(Measure.pi μ') := by
        rw [integral_prod_symm _ hFint]
      set c : (∀ j, E' j) → ℝ := fun r => ∫ x, g (e.symm (x, r)) ∂(μ 0) with hc_def
      have hGmeas : Measurable (fun p : E 0 × (∀ j, E' j) => g (e.symm p)) :=
        hg.comp e.symm.measurable
      have hGint : Integrable (fun p : E 0 × (∀ j, E' j) => g (e.symm p))
          ((μ 0).prod (Measure.pi μ')) :=
        Integrable.of_bound hGmeas.aestronglyMeasurable C (Filter.Eventually.of_forall (fun p => by
          rw [Real.norm_eq_abs]; exact hbdd (e.symm p)))
      have hc_meas : Measurable c := by
        rw [hc_def]
        exact hGmeas.stronglyMeasurable.integral_prod_left'.measurable
      have hslice_meas : ∀ r : ∀ j, E' j, Measurable (fun x : E 0 => g (e.symm (x, r))) := by
        intro r
        exact hg.comp (e.symm.measurable.comp measurable_prodMk_right)
      have hslice_int : ∀ r : ∀ j, E' j, Integrable (fun x : E 0 => g (e.symm (x, r))) (μ 0) := by
        intro r
        exact Integrable.of_bound (hslice_meas r).aestronglyMeasurable C
          (Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs]; exact hbdd (e.symm (x, r))))
      have hc_bdd : ∀ r, |c r| ≤ C := by
        intro r
        have h1 : |c r| ≤ ∫ x, |g (e.symm (x, r))| ∂(μ 0) := by
          rw [hc_def]
          exact abs_integral_le_integral_abs
        have h2 : ∫ x, |g (e.symm (x, r))| ∂(μ 0) ≤ ∫ x, C ∂(μ 0) := by
          apply integral_mono (hslice_int r).norm (integrable_const C)
          intro x
          exact hbdd (e.symm (x, r))
        have h3 : ∫ x, C ∂(μ 0) = C := by simp
        linarith
      have hc_hr : ∀ (r r' : ∀ j, E' j) (j : Fin b),
          (∀ j', j' ≠ j → r j' = r' j') → |c r' - c r| ≤ Lr := by
        intro r r' j hj
        have hsub : c r' - c r
            = ∫ x, (g (e.symm (x, r')) - g (e.symm (x, r))) ∂(μ 0) := by
          rw [hc_def]
          rw [integral_sub (hslice_int r') (hslice_int r)]
        rw [hsub]
        calc |∫ x, (g (e.symm (x, r')) - g (e.symm (x, r))) ∂(μ 0)|
            ≤ ∫ x, |g (e.symm (x, r')) - g (e.symm (x, r))| ∂(μ 0) :=
              abs_integral_le_integral_abs
          _ ≤ ∫ x, Lr ∂(μ 0) := by
              apply integral_mono ((hslice_int r').sub (hslice_int r)).norm (integrable_const Lr)
              intro x
              apply hr (e.symm (x, r)) (e.symm (x, r')) (((0 : Fin (b+1)).succAbove j))
              intro i' hi'
              rcases Fin.eq_self_or_eq_succAbove 0 i' with h | ⟨k, rfl⟩
              · rw [h, e_symm x r, e_symm x r', Fin.insertNth_apply_same, Fin.insertNth_apply_same]
              · rw [e_symm x r, e_symm x r', Fin.insertNth_apply_succAbove,
                  Fin.insertNth_apply_succAbove]
                exact hj k (fun hkj => hi' (by rw [hkj]))
          _ = Lr := by simp
      have hc_mean : ∫ r, c r ∂(Measure.pi μ') = 0 := by
        have h : ∫ r, c r ∂(Measure.pi μ')
            = ∫ p : E 0 × (∀ j, E' j), g (e.symm p) ∂((μ 0).prod (Measure.pi μ')) := by
          rw [hc_def]
          rw [integral_prod_symm _ hGint]
        rw [h, he.symm.integral_comp']
        exact hmean
      have hstep : ∀ r, ∫ x, Real.exp (θ * g (e.symm (x, r))) ∂(μ 0)
          ≤ Real.exp (θ * c r) * Real.exp (θ ^ 2 * Lr ^ 2 / 8) := by
        intro r
        have hshift_meas : Measurable (fun x : E 0 => g (e.symm (x, r)) - c r) :=
          (hslice_meas r).sub measurable_const
        have hshift_bd : ∀ x x',
            |(g (e.symm (x, r)) - c r) - (g (e.symm (x', r)) - c r)| ≤ Lr := by
          intro x x'
          have h1 : |g (e.symm (x, r)) - g (e.symm (x', r))| ≤ Lr := by
            have h := hr (e.symm (x, r)) (e.symm (x', r)) 0 (by
              intro i' hi'
              rcases Fin.eq_self_or_eq_succAbove 0 i' with h | ⟨k, rfl⟩
              · exact absurd h hi'
              · rw [e_symm x r, e_symm x' r, Fin.insertNth_apply_succAbove,
                  Fin.insertNth_apply_succAbove])
            rwa [abs_sub_comm] at h
          have harg : (g (e.symm (x, r)) - c r) - (g (e.symm (x', r)) - c r)
              = g (e.symm (x, r)) - g (e.symm (x', r)) := by ring
          rw [harg]
          exact h1
        have hshift_mean : ∫ x, (g (e.symm (x, r)) - c r) ∂(μ 0) = 0 := by
          rw [integral_sub (hslice_int r) (integrable_const _)]
          have hc : ∫ x, c r ∂(μ 0) = c r := by simp
          rw [hc]
          rw [hc_def]
          ring
        have hhoef := hoeffding_range (ν := μ 0) hLr hshift_meas hshift_bd hshift_mean θ
        have hfun : (fun x : E 0 => Real.exp (θ * g (e.symm (x, r))))
            = fun x => Real.exp (θ * c r) * Real.exp (θ * (g (e.symm (x, r)) - c r)) := by
          funext x
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hfun, integral_const_mul]
        exact mul_le_mul_of_nonneg_left hhoef (Real.exp_pos _).le
      have hInner_meas : Measurable
          (fun r => ∫ x, Real.exp (θ * g (e.symm (x, r))) ∂(μ 0)) :=
        hFmeas.stronglyMeasurable.integral_prod_left'.measurable
      have hexp_slice_int : ∀ r : ∀ j, E' j,
          Integrable (fun x : E 0 => Real.exp (θ * g (e.symm (x, r)))) (μ 0) := by
        intro r
        refine Integrable.of_bound ?_ (Real.exp (|θ| * C)) (Filter.Eventually.of_forall ?_)
        · exact (Real.measurable_exp.comp (measurable_const.mul (hslice_meas r))).aestronglyMeasurable
        · intro x
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact hexp_bound (x, r)
      have hInner_int : Integrable (fun r => ∫ x, Real.exp (θ * g (e.symm (x, r))) ∂(μ 0))
          (Measure.pi μ') := by
        refine Integrable.of_bound hInner_meas.aestronglyMeasurable (Real.exp (|θ| * C)) ?_
        filter_upwards with r
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => (Real.exp_pos _).le))]
        calc ∫ x, Real.exp (θ * g (e.symm (x, r))) ∂(μ 0)
            ≤ ∫ x, Real.exp (|θ| * C) ∂(μ 0) := by
              apply integral_mono (hexp_slice_int r) (integrable_const _)
              intro x
              exact hexp_bound (x, r)
          _ = Real.exp (|θ| * C) := by simp
      have hRHS_int : Integrable
          (fun r => Real.exp (θ * c r) * Real.exp (θ ^ 2 * Lr ^ 2 / 8)) (Measure.pi μ') := by
        refine Integrable.of_bound ?_ (Real.exp (|θ| * C) * Real.exp (θ ^ 2 * Lr ^ 2 / 8)) ?_
        · exact ((Real.measurable_exp.comp (measurable_const.mul hc_meas)).mul
            measurable_const).aestronglyMeasurable
        · filter_upwards with r
          rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
          have hcθ : Real.exp (θ * c r) ≤ Real.exp (|θ| * C) := by
            apply Real.exp_le_exp.mpr
            calc θ * c r ≤ |θ * c r| := le_abs_self _
              _ = |θ| * |c r| := abs_mul θ _
              _ ≤ |θ| * C := mul_le_mul_of_nonneg_left (hc_bdd r) (abs_nonneg θ)
          have hK : 0 ≤ Real.exp (θ ^ 2 * Lr ^ 2 / 8) := (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hcθ hK
      have h3 : ∫ r, ∫ x, Real.exp (θ * g (e.symm (x, r))) ∂(μ 0) ∂(Measure.pi μ')
          ≤ ∫ r, Real.exp (θ * c r) * Real.exp (θ ^ 2 * Lr ^ 2 / 8) ∂(Measure.pi μ') := by
        apply integral_mono_ae hInner_int hRHS_int
        filter_upwards with r using hstep r
      have h4 : ∫ r, Real.exp (θ * c r) * Real.exp (θ ^ 2 * Lr ^ 2 / 8) ∂(Measure.pi μ')
          = Real.exp (θ ^ 2 * Lr ^ 2 / 8) * ∫ r, Real.exp (θ * c r) ∂(Measure.pi μ') := by
        have hfun : (fun r => Real.exp (θ * c r) * Real.exp (θ ^ 2 * Lr ^ 2 / 8))
            = fun r => Real.exp (θ ^ 2 * Lr ^ 2 / 8) * Real.exp (θ * c r) := by
          funext r
          ring
        rw [hfun, integral_const_mul]
      have hIH := ih E' μ' Lr hLr c hc_meas hc_hr hc_mean θ
      have hstep1 : ∫ R, Real.exp (θ * g R) ∂Measure.pi μ
          = ∫ r, ∫ x, Real.exp (θ * g (e.symm (x, r))) ∂(μ 0) ∂(Measure.pi μ') := by
        rw [h1, h2]
      have hstep2 : ∫ r, ∫ x, Real.exp (θ * g (e.symm (x, r))) ∂(μ 0) ∂(Measure.pi μ')
          ≤ ∫ r, Real.exp (θ * c r) * Real.exp (θ ^ 2 * Lr ^ 2 / 8) ∂(Measure.pi μ') := h3
      have hstep3 : ∫ r, Real.exp (θ * c r) * Real.exp (θ ^ 2 * Lr ^ 2 / 8) ∂(Measure.pi μ')
          = Real.exp (θ ^ 2 * Lr ^ 2 / 8) * ∫ r, Real.exp (θ * c r) ∂(Measure.pi μ') := h4
      have hstep4 : Real.exp (θ ^ 2 * Lr ^ 2 / 8) * ∫ r, Real.exp (θ * c r) ∂(Measure.pi μ')
          ≤ Real.exp (θ ^ 2 * Lr ^ 2 / 8)
              * Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hIH (Real.exp_pos _).le
      have hstep5 : Real.exp (θ ^ 2 * Lr ^ 2 / 8) * Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
          = Real.exp (θ ^ 2 * (↑(b + 1) : ℝ) * Lr ^ 2 / 8) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      exact (le_of_eq hstep1).trans
        (hstep2.trans ((le_of_eq hstep3).trans (hstep4.trans (le_of_eq hstep5))))


theorem lemma_4_2 (D N b : ℕ) (hDN : D ≤ N)
    (E : Fin b → Type) [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, MeasureTheory.Measure (E i)) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (F : (Fin D ↪ Fin N) → (∀ i, E i) → ℝ) (hF : ∀ π, Measurable (F π))
    (Lp Lr : ℝ) (hLp : 0 ≤ Lp) (hLr : 0 ≤ Lr)
    (hp : ∀ (π : Fin D ↪ Fin N) (R : ∀ i, E i) (a c : Fin N),
      |F (π.trans (Equiv.swap a c).toEmbedding) R - F π R| ≤ Lp)
    (hr : ∀ (π : Fin D ↪ Fin N) (R R' : ∀ i, E i) (i : Fin b), (∀ i' , i' ≠ i → R i' = R' i') →
      |F π R' - F π R| ≤ Lr)
    (hpos : 0 < (D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2) (t : ℝ) (ht : 0 < t) :
    let P := MeasureTheory.Measure.pi μ
    let card : ℝ := Fintype.card (Fin D ↪ Fin N)
    let EF : ℝ := (∑ π : Fin D ↪ Fin N, ∫ R, F π R ∂P) / card
    (∑ π : Fin D ↪ Fin N, (P {R | t ≤ F π R - EF}).toReal) / card ≤
      Real.exp (-(2 * t ^ 2 / ((D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2))) := by
  intro P card EF
  haveI hPprob : IsProbabilityMeasure P := by
    rw [show P = Measure.pi μ from rfl]
    infer_instance
  -- cardinality
  have hcard_nat : 0 < Fintype.card (Fin D ↪ Fin N) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨Fin.castLE hDN, Fin.castLE_injective hDN⟩⟩
  have hcard_pos : 0 < card := by
    rw [show card = ((Fintype.card (Fin D ↪ Fin N) : ℕ) : ℝ) from rfl]
    exact_mod_cast hcard_nat
  have hcard_ne : card ≠ 0 := ne_of_gt hcard_pos
  set C : ℝ := (D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2 with hC
  have hCpos : 0 < C := by rw [hC]; exact hpos
  set θ : ℝ := 4 * t / C with hθ
  have hθpos : 0 < θ := by
    rw [hθ]
    exact div_pos (by linarith) hCpos
  -- nonempty coordinates and a base point
  haveI hne : ∀ i, Nonempty (E i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  let R0 : ∀ i, E i := fun i => Classical.choice (hne i)
  have hbdd : ∀ (π : Fin D ↪ Fin N) (R : ∀ i, E i),
      |F π R| ≤ |F π R0| + (b : ℝ) * Lr := by
    intro π R
    have h := abs_sub_le_of_coord Lr b E (F π) R R0 (hr π)
    have h2 : |F π R| ≤ |F π R0| + |F π R - F π R0| := by
      have harg : F π R = F π R0 + (F π R - F π R0) := by ring
      calc |F π R| = |F π R0 + (F π R - F π R0)| := by conv_lhs => rw [harg]
        _ ≤ |F π R0| + |F π R - F π R0| := abs_add_le _ _
    linarith
  have hFint : ∀ π : Fin D ↪ Fin N, Integrable (F π) P := by
    intro π
    refine Integrable.of_bound (hF π).aestronglyMeasurable
      (|F π R0| + (b : ℝ) * Lr) ?_
    filter_upwards with R
    rw [Real.norm_eq_abs]
    exact hbdd π R
  -- the averaged function
  set f : (Fin D ↪ Fin N) → ℝ := fun π => ∫ R, F π R ∂P with hf
  have hEF_eq : EF = (∑ π : Fin D ↪ Fin N, f π) / card := rfl
  have hf_hr : ∀ (π : Fin D ↪ Fin N) (a c : Fin N),
      |f (π.trans (Equiv.swap a c).toEmbedding) - f π| ≤ Lp := by
    intro π a c
    have hsub : f (π.trans (Equiv.swap a c).toEmbedding) - f π
        = ∫ R, (F (π.trans (Equiv.swap a c).toEmbedding) R - F π R) ∂P := by
      rw [hf]
      exact (integral_sub (hFint _) (hFint _)).symm
    rw [hsub]
    calc |∫ R, (F (π.trans (Equiv.swap a c).toEmbedding) R - F π R) ∂P|
        ≤ ∫ R, |F (π.trans (Equiv.swap a c).toEmbedding) R - F π R| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ R, Lp ∂P := by
          apply integral_mono ((hFint _).sub (hFint _)).norm (integrable_const Lp)
          intro R
          exact hp π R a c
      _ = Lp := by simp
  -- product-side Hoeffding for each fixed pi
  have hprod : ∀ π : Fin D ↪ Fin N,
      ∫ R, Real.exp (θ * (F π R - f π)) ∂P
        ≤ Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8) := by
    intro π
    have hmean : ∫ R, (F π R - f π) ∂P = 0 := by
      rw [integral_sub (hFint π) (integrable_const _)]
      simp only [hf]
      simp
    have hhr : ∀ (R R' : ∀ i, E i) (i : Fin b),
        (∀ i', i' ≠ i → R i' = R' i') → |(F π R' - f π) - (F π R - f π)| ≤ Lr := by
      intro R R' i h
      have h' := hr π R R' i h
      have harg : (F π R' - f π) - (F π R - f π) = F π R' - F π R := by ring
      rw [harg]
      exact h'
    have := product_part b E μ Lr hLr (fun R => F π R - f π)
      ((hF π).sub measurable_const) hhr hmean θ
    rw [show P = Measure.pi μ from rfl]
    exact this
  -- the pi-side bound
  have hpi' : (∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - EF))) / card
      ≤ Real.exp (θ ^ 2 * (D : ℝ) * Lp ^ 2 / 8) := by
    rw [hEF_eq]
    exact pi_part N D hDN f Lp hLp θ hf_hr
  -- Chernoff bound
  have hExpInt : ∀ π : Fin D ↪ Fin N,
      Integrable (fun R => Real.exp (θ * (F π R - EF))) P := by
    intro π
    set B : ℝ := |F π R0| + (b : ℝ) * Lr + |EF| with hB
    refine Integrable.of_bound ?_ (Real.exp (|θ| * B)) ?_
    · exact (Real.measurable_exp.comp
        (measurable_const.mul ((hF π).sub measurable_const))).aestronglyMeasurable
    · filter_upwards with R
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc θ * (F π R - EF) ≤ |θ * (F π R - EF)| := le_abs_self _
        _ = |θ| * |F π R - EF| := abs_mul _ _
        _ ≤ |θ| * B := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg θ)
            rw [hB]
            calc |F π R - EF| ≤ |F π R| + |EF| := by
                  have h := abs_add_le (F π R) (-EF)
                  simpa [sub_eq_add_neg] using h
              _ ≤ (|F π R0| + (b : ℝ) * Lr) + |EF| := by linarith [hbdd π R]
  have hchernoff : ∀ π : Fin D ↪ Fin N,
      (P {R | t ≤ F π R - EF}).toReal
        ≤ Real.exp (-(θ * t)) * ∫ R, Real.exp (θ * (F π R - EF)) ∂P := by
    intro π
    have hset : {R | t ≤ F π R - EF}
        = {R | Real.exp (θ * t) ≤ Real.exp (θ * (F π R - EF))} := by
      ext R
      simp only [Set.mem_setOf_eq, Real.exp_le_exp]
      constructor
      · intro h; exact mul_le_mul_of_nonneg_left h hθpos.le
      · intro h; exact le_of_mul_le_mul_left h hθpos
    rw [hset]
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (f := fun R => Real.exp (θ * (F π R - EF)))
      (Filter.Eventually.of_forall (fun R => (Real.exp_pos _).le)) (hExpInt π)
      (Real.exp (θ * t))
    have h1 : P.real {R | Real.exp (θ * t) ≤ Real.exp (θ * (F π R - EF))}
        ≤ (∫ R, Real.exp (θ * (F π R - EF)) ∂P) / Real.exp (θ * t) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      rw [mul_comm]
      exact hmarkov
    rw [show (P {R | Real.exp (θ * t) ≤ Real.exp (θ * (F π R - EF))}).toReal
        = P.real {R | Real.exp (θ * t) ≤ Real.exp (θ * (F π R - EF))} from rfl]
    refine h1.trans ?_
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_comm]
  -- splitting the exponent
  have hsplit : ∀ π : Fin D ↪ Fin N,
      ∫ R, Real.exp (θ * (F π R - EF)) ∂P
        = Real.exp (θ * (f π - EF)) * ∫ R, Real.exp (θ * (F π R - f π)) ∂P := by
    intro π
    have hfun : (fun R => Real.exp (θ * (F π R - EF)))
        = fun R => Real.exp (θ * (f π - EF)) * Real.exp (θ * (F π R - f π)) := by
      funext R
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfun, integral_const_mul]
  have hbound : ∀ π : Fin D ↪ Fin N,
      ∫ R, Real.exp (θ * (F π R - EF)) ∂P
        ≤ Real.exp (θ * (f π - EF)) * Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8) := by
    intro π
    rw [hsplit π]
    exact mul_le_mul_of_nonneg_left (hprod π) (Real.exp_pos _).le
  have hsum : ∑ π : Fin D ↪ Fin N, ∫ R, Real.exp (θ * (F π R - EF)) ∂P
      ≤ Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
          * ∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - EF)) := by
    calc ∑ π : Fin D ↪ Fin N, ∫ R, Real.exp (θ * (F π R - EF)) ∂P
        ≤ ∑ π : Fin D ↪ Fin N,
            Real.exp (θ * (f π - EF)) * Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8) :=
          Finset.sum_le_sum (fun π _ => hbound π)
      _ = (∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - EF)))
            * Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8) := by rw [Finset.sum_mul]
      _ = Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
            * ∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - EF)) := by rw [mul_comm]
  have hA : ∑ π : Fin D ↪ Fin N, (P {R | t ≤ F π R - EF}).toReal
      ≤ Real.exp (-(θ * t))
          * ∑ π : Fin D ↪ Fin N, ∫ R, Real.exp (θ * (F π R - EF)) ∂P := by
    calc ∑ π : Fin D ↪ Fin N, (P {R | t ≤ F π R - EF}).toReal
        ≤ ∑ π : Fin D ↪ Fin N,
            Real.exp (-(θ * t)) * ∫ R, Real.exp (θ * (F π R - EF)) ∂P :=
          Finset.sum_le_sum (fun π _ => hchernoff π)
      _ = Real.exp (-(θ * t))
            * ∑ π : Fin D ↪ Fin N, ∫ R, Real.exp (θ * (F π R - EF)) ∂P := by
          rw [Finset.mul_sum]
  -- assemble
  have hSdiv : (∑ π : Fin D ↪ Fin N, ∫ R, Real.exp (θ * (F π R - EF)) ∂P) / card
      ≤ Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
          * ((∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - EF))) / card) := by
    have h1 := div_le_div_of_nonneg_right hsum hcard_pos.le
    calc (∑ π : Fin D ↪ Fin N, ∫ R, Real.exp (θ * (F π R - EF)) ∂P) / card
        ≤ (Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
            * ∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - EF))) / card := h1
      _ = Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
            * ((∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - EF))) / card) := by ring
  have hfinal : (∑ π : Fin D ↪ Fin N, (P {R | t ≤ F π R - EF}).toReal) / card
      ≤ Real.exp (-(θ * t))
          * (Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
              * Real.exp (θ ^ 2 * (D : ℝ) * Lp ^ 2 / 8)) := by
    have h1 := div_le_div_of_nonneg_right hA hcard_pos.le
    have hK : 0 ≤ Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8) := (Real.exp_pos _).le
    have hCh : 0 ≤ Real.exp (-(θ * t)) := (Real.exp_pos _).le
    calc (∑ π : Fin D ↪ Fin N, (P {R | t ≤ F π R - EF}).toReal) / card
        ≤ (Real.exp (-(θ * t))
            * ∑ π : Fin D ↪ Fin N, ∫ R, Real.exp (θ * (F π R - EF)) ∂P) / card := h1
      _ = Real.exp (-(θ * t))
            * ((∑ π : Fin D ↪ Fin N, ∫ R, Real.exp (θ * (F π R - EF)) ∂P) / card) := by
          ring
      _ ≤ Real.exp (-(θ * t))
            * (Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
                * ((∑ π : Fin D ↪ Fin N, Real.exp (θ * (f π - EF))) / card)) := by
          apply mul_le_mul_of_nonneg_left hSdiv hCh
      _ ≤ Real.exp (-(θ * t))
            * (Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
                * Real.exp (θ ^ 2 * (D : ℝ) * Lp ^ 2 / 8)) := by
          apply mul_le_mul_of_nonneg_left _ hCh
          exact mul_le_mul_of_nonneg_left hpi' hK
  -- final exponent computation
  have hexp : Real.exp (-(θ * t))
        * (Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
            * Real.exp (θ ^ 2 * (D : ℝ) * Lp ^ 2 / 8))
      = Real.exp (-(2 * t ^ 2 / ((D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hθ, hC]
    have hCne : (D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2 ≠ 0 := ne_of_gt hpos
    field_simp [hCne]
    ring
  calc (∑ π : Fin D ↪ Fin N, (P {R | t ≤ F π R - EF}).toReal) / card
      ≤ Real.exp (-(θ * t))
          * (Real.exp (θ ^ 2 * (b : ℝ) * Lr ^ 2 / 8)
              * Real.exp (θ ^ 2 * (D : ℝ) * Lp ^ 2 / 8)) := hfinal
    _ = Real.exp (-(2 * t ^ 2 / ((D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2))) := hexp


end
end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
theorem solution (D N b : ℕ) (hDN : D ≤ N)
    (E : Fin b → Type) [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, MeasureTheory.Measure (E i)) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (F : (Fin D ↪ Fin N) → (∀ i, E i) → ℝ) (hF : ∀ π, Measurable (F π))
    (Lp Lr : ℝ) (hLp : 0 ≤ Lp) (hLr : 0 ≤ Lr)
    (hp : ∀ (π : Fin D ↪ Fin N) (R : ∀ i, E i) (a c : Fin N),
      |F (π.trans (Equiv.swap a c).toEmbedding) R - F π R| ≤ Lp)
    (hr : ∀ (π : Fin D ↪ Fin N) (R R' : ∀ i, E i) (i : Fin b), (∀ i' , i' ≠ i → R i' = R' i') →
      |F π R' - F π R| ≤ Lr)
    (hpos : 0 < (D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2) (t : ℝ) (ht : 0 < t) :
    let P := MeasureTheory.Measure.pi μ
    let card : ℝ := Fintype.card (Fin D ↪ Fin N)
    let EF : ℝ := (∑ π : Fin D ↪ Fin N, ∫ R, F π R ∂P) / card
    (∑ π : Fin D ↪ Fin N, (P {R | t ≤ F π R - EF}).toReal) / card ≤
      Real.exp (-(2 * t ^ 2 / ((D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2))) :=
  LinearSetReconciliation327.Main.lemma_4_2 D N b hDN E μ F hF Lp Lr hLp hLr hp hr hpos t ht
