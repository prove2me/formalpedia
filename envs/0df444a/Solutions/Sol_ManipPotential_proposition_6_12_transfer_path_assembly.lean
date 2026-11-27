-- Prove2me | solution 1 for ManipPotential.proposition_6_12_transfer_path_assembly
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:09:09.71081+00:00
-- url     : https://prove2.me/submissions/7e4139d7-d847-4ca9-8cfe-c0a9e3143b7d

import Mathlib
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_TransferStep
import Definitions.Def_ManipPotential_referenceCurve

namespace TPAHelpers
open ManipPotential

def toR {ι : Type*} (Q : ι → ℚ) : ι → ℝ := fun r => (Q r : ℝ)

lemma toR_add {ι : Type*} (A B : ι → ℚ) : toR (A + B) = toR A + toR B := by
  funext r; simp [toR]

lemma toR_smul {ι : Type*} (a : ℚ) (A : ι → ℚ) : toR (a • A) = (a : ℝ) • toR A := by
  funext r; simp [toR]

lemma toR_nsmul {ι : Type*} (n : ℕ) (A : ι → ℚ) : toR (n • A) = (n : ℝ) • toR A := by
  funext r; simp [toR]

lemma toR_zero {ι : Type*} : toR (0 : ι → ℚ) = 0 := by
  funext r; simp [toR]

lemma toR_sum {ι α : Type*} (s : Finset α) (f : α → ι → ℚ) :
    toR (∑ x ∈ s, f x) = ∑ x ∈ s, toR (f x) := by
  funext r; simp [toR, Finset.sum_apply]

lemma unitVec_nonneg {m : ℕ} (a b : Ranking m) : (0 : ℝ) ≤ unitVec a b := by
  simp only [unitVec, Pi.single_apply]; split_ifs <;> norm_num

lemma exists_rat_move {m : ℕ} (K : ℕ) (i j : Fin m) (u : Ranking m → ℝ)
    (hu : u ∈ TransferVectors ((K : ℝ) + 1) i j) :
    ∃ w : Ranking m → ℚ, toR w = u ∧ ∀ (Q : Ranking m → ℚ) (a : ℚ), 0 < a →
      (∀ r, a * ((K : ℚ) + 1) ≤ Q r) → TransferStep K i j Q (Q + a • w) := by
  have hK : (0 : ℚ) ≤ K := by positivity
  rcases hu with ⟨r, s, hrs, rfl⟩ | ⟨r, s, hrs, rfl⟩
  · refine ⟨((K : ℚ) + 1) • unitVec r - unitVec s, ?_, ?_⟩
    · funext x; simp only [toR, unitVec, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul]
      split_ifs <;> push_cast <;> ring
    · intro Q a ha hQ
      refine ⟨r, s, a, ha, Or.inl ⟨hrs, rfl, ?_⟩⟩
      intro x
      have := hQ x
      simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, unitVec, Pi.single_apply,
        smul_eq_mul]
      split_ifs <;> nlinarith
  · refine ⟨unitVec s - ((K : ℚ) + 1) • unitVec r, ?_, ?_⟩
    · funext x; simp only [toR, unitVec, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul]
      split_ifs <;> push_cast <;> ring
    · intro Q a ha hQ
      refine ⟨r, s, a, ha, Or.inr ⟨hrs, rfl, ?_⟩⟩
      intro x
      have := hQ x
      simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, unitVec, Pi.single_apply,
        smul_eq_mul]
      split_ifs <;> nlinarith

/-- Splitting a periodic sum into full rounds and a partial round. -/
lemma sum_range_mod {M : Type*} [AddCommMonoid M] (f : ℕ → M) (q n h : ℕ) (hh : h ≤ q) :
    ∑ l ∈ Finset.range (n * q + h), f (l % q) =
      n • (∑ l ∈ Finset.range q, f l) + ∑ l ∈ Finset.range h, f l := by
  have hfull : ∀ n : ℕ, ∑ l ∈ Finset.range (n * q), f (l % q) =
      n • (∑ l ∈ Finset.range q, f l) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
      congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_range] at hx
      rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
  rw [Finset.sum_range_add, hfull]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_range] at hx
  rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (lt_of_lt_of_le hx hh)]

end TPAHelpers

open ManipPotential TPAHelpers

theorem solution {m : ℕ} [NeZero m]
    (K : ℕ) (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (U : Set ((ExtRanking m → ℝ) × ℝ)) (hUopen : IsOpen U)
    (z₀ : ((ExtRanking m → ℝ) × ℝ)) (hzU : z₀ ∈ U)
    (hzdiff : DifferentiableAt ℝ G z₀)
    (hpos : ∀ z ∈ U, ∀ r, 1 < G z r) (i j : Fin m) (hij : i ≠ j)
    (v : ((ExtRanking m → ℝ) × ℝ)) (q : ℕ)
    (u : Fin q → Ranking m → ℝ) (β : Fin q → ℚ)
    (hu : ∀ h, u h ∈ TransferVectors ((K : ℝ) + 1) i j)
    (hβ : ∀ h, 0 ≤ β h)
    (herr : ‖(∑ h, (β h : ℝ) • u h) -
      ((fderiv ℝ G z₀) v - (unitVec (ell i) - unitVec (ell j)))‖ <
        1 / (64 * kappa m K)) :
    ∃ (ρ : ℚ) (L : ℕ) (Q : ℕ → Ranking m → ℚ),
      0 < ρ ∧
      (ρ : ℝ) / (4 * kappa m K) < 1 / 2 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, z₀ + (t * (ρ : ℝ)) • v ∈ U) ∧
      (∀ k ≤ L, ∃ t ∈ Set.Icc (0 : ℝ) 1,
        ‖(fun r => (Q k r : ℝ)) - referenceCurve K G z₀ v i j (ρ : ℝ) t‖ <
          ((ρ : ℝ) / (4 * kappa m K)) / 4) ∧
      ‖(fun r => (Q 0 r : ℝ)) - referenceCurve K G z₀ v i j (ρ : ℝ) 0‖ <
          ((ρ : ℝ) / (4 * kappa m K)) / 4 ∧
      ‖(fun r => (Q L r : ℝ)) - referenceCurve K G z₀ v i j (ρ : ℝ) 1‖ <
          ((ρ : ℝ) / (4 * kappa m K)) / 4 ∧
      (∀ k < L, TransferStep K i j (Q k) (Q (k + 1))) := by
  classical
  set κ := kappa m K with hκdef
  have hκ : 0 < κ := by simp only [hκdef, kappa]; positivity
  set η : ℝ := 1 / (64 * κ) with hηdef
  have hη : 0 < η := by positivity
  set D := fderiv ℝ G z₀ with hDdef
  set w : Ranking m → ℝ := D v - (unitVec (ell i) - unitVec (ell j)) with hwdef
  -- rational transfer moves
  have hmv := fun h => exists_rat_move K i j (u h) (hu h)
  choose û hûR hûT using hmv
  -- perturb β to strictly positive coefficients
  set S : ℝ := ∑ h, ‖u h‖ with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  set c : Ranking m → ℝ := ∑ h, (β h : ℝ) • u h with hcdef
  have hgap : 0 < η - ‖c - w‖ := by linarith
  obtain ⟨τ, hτ0, hτ⟩ : ∃ τ : ℚ, 0 < τ ∧ (τ : ℝ) < (η - ‖c - w‖) / (S + 1) := by
    obtain ⟨τ, h1, h2⟩ := exists_rat_btwn (show (0 : ℝ) < (η - ‖c - w‖) / (S + 1) by positivity)
    exact ⟨τ, by exact_mod_cast h1, h2⟩
  set β' : Fin q → ℚ := fun h => β h + τ with hβ'def
  have hβ'pos : ∀ h, 0 < β' h := fun h => by have := hβ h; simp only [hβ'def]; linarith
  set c' : Ranking m → ℝ := ∑ h, (β' h : ℝ) • u h with hc'def
  have hc' : ‖c' - w‖ < η := by
    have hsplit : c' - w = (c - w) + (τ : ℝ) • ∑ h, u h := by
      simp only [hc'def, hcdef, hβ'def, Rat.cast_add, add_smul, Finset.sum_add_distrib,
        Finset.smul_sum]
      abel
    rw [hsplit]
    have hτ' : (τ : ℝ) * (S + 1) < η - ‖c - w‖ := by rwa [lt_div_iff₀ (by positivity)] at hτ
    have hτpos : (0 : ℝ) < τ := by exact_mod_cast hτ0
    calc ‖(c - w) + (τ : ℝ) • ∑ h, u h‖ ≤ ‖c - w‖ + τ * S := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hτpos.le]
          gcongr
          exact norm_sum_le _ _
      _ < η := by nlinarith
  clear_value c c'
  -- number of rounds
  set S' : ℝ := ∑ h, (β' h : ℝ) * ‖u h‖ with hS'def
  have hS' : 0 ≤ S' := Finset.sum_nonneg fun h _ =>
    mul_nonneg (by exact_mod_cast (hβ'pos h).le) (norm_nonneg _)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, S' / η < N := exists_nat_gt _
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hNS : S' / N < η := by
    rw [div_lt_iff₀ hNpos]; rw [div_lt_iff₀ hη] at hN; linarith
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  -- bound on the coefficients
  set Bs : ℚ := ∑ h, β' h with hBsdef
  have hBs : ∀ h, β' h ≤ Bs := fun h =>
    Finset.single_le_sum (fun h _ => (hβ'pos h).le) (Finset.mem_univ h)
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun h _ => (hβ'pos h).le
  clear_value Bs S S'
  -- differentiability
  have hD : HasFDerivAt G D z₀ := hzdiff.hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hD
  have hev := hD.def (show 0 < η / (‖v‖ + 1) by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.1 hUopen z₀ hzU
  -- choice of ρ
  set lamR : ℝ := (K : ℝ) + 1 with hlamR
  have hlam : (1 : ℝ) ≤ lamR := le_add_of_nonneg_left (Nat.cast_nonneg K)
  set ρmax : ℝ := min (min (δ₁ / (‖v‖ + 1)) (δ₂ / (‖v‖ + 1)))
      (min (2 * κ) (1 / (4 * lamR * ((Bs : ℝ) + 1)))) with hρmax
  have hρmax0 : 0 < ρmax := by
    have : (0 : ℝ) ≤ Bs := by exact_mod_cast hBs0
    simp only [hρmax]; positivity
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_rat_btwn hρmax0
  have hρpos : (0 : ℚ) < ρ := by exact_mod_cast hρ0
  have hρ_1 : (ρ : ℝ) < δ₁ / (‖v‖ + 1) :=
    lt_of_lt_of_le hρ1 ((min_le_left _ _).trans (min_le_left _ _))
  have hρ_2 : (ρ : ℝ) < δ₂ / (‖v‖ + 1) :=
    lt_of_lt_of_le hρ1 ((min_le_left _ _).trans (min_le_right _ _))
  have hρ_3 : (ρ : ℝ) < 2 * κ :=
    lt_of_lt_of_le hρ1 ((min_le_right _ _).trans (min_le_left _ _))
  have hρ_4 : (ρ : ℝ) < 1 / (4 * lamR * ((Bs : ℝ) + 1)) :=
    lt_of_lt_of_le hρ1 ((min_le_right _ _).trans (min_le_right _ _))
  clear_value ρmax lamR
  -- the segment
  have hseg_norm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(t * (ρ : ℝ)) • v‖ ≤ ρ * ‖v‖ := by
    intro t ht
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg ht.1 hρ0.le)]
    have : t * (ρ : ℝ) ≤ ρ := by nlinarith [ht.2]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, z₀ + (t * (ρ : ℝ)) • v ∈ U := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have h1 := hseg_norm t ht
    have h2 : (ρ : ℝ) * (‖v‖ + 1) < δ₁ := by rwa [lt_div_iff₀ (by positivity)] at hρ_1
    nlinarith [norm_nonneg v]
  -- remainder
  set B := referenceCurve K G z₀ v i j (ρ : ℝ) with hBdef
  set R : ℝ → Ranking m → ℝ := fun t =>
    G (z₀ + (t * (ρ : ℝ)) • v) - G z₀ - D ((t * (ρ : ℝ)) • v) with hRdef
  have hRbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖R t‖ < η * ρ := by
    intro t ht
    have h1 := hseg_norm t ht
    have h2 : (ρ : ℝ) * (‖v‖ + 1) < δ₂ := by rwa [lt_div_iff₀ (by positivity)] at hρ_2
    have hdist : dist ((t * (ρ : ℝ)) • v) 0 < δ₂ := by
      rw [dist_zero_right]; nlinarith [norm_nonneg v]
    have h3 := hδ₂' hdist
    simp only [hRdef]
    calc ‖G (z₀ + (t * (ρ : ℝ)) • v) - G z₀ - D ((t * (ρ : ℝ)) • v)‖
        ≤ η / (‖v‖ + 1) * ‖(t * (ρ : ℝ)) • v‖ := h3
      _ ≤ η / (‖v‖ + 1) * (ρ * ‖v‖) := by gcongr
      _ = η * ρ * (‖v‖ / (‖v‖ + 1)) := by ring
      _ < η * ρ * 1 := by
          gcongr
          rw [div_lt_one (by positivity)]; linarith
      _ = η * ρ := by ring
  have hBexp : ∀ t, B t = B 0 + (t * (ρ : ℝ)) • w + R t := by
    intro t
    simp only [hBdef, referenceCurve, hRdef, hwdef, map_smul, zero_mul, zero_smul, add_zero,
      sub_zero, one_smul]
    module
  clear_value R B w
  -- rational starting point
  have hηρ : 0 < η * ρ := by positivity
  have hQ0ex : ∀ r, ∃ x : ℚ, |(x : ℝ) - B 0 r| < η * ρ := by
    intro r
    obtain ⟨x, h1, h2⟩ := exists_rat_btwn (show B 0 r < B 0 r + η * ρ by linarith)
    exact ⟨x, by rw [abs_lt]; constructor <;> linarith⟩
  choose Q0 hQ0 using hQ0ex
  have hQ0n : ‖toR Q0 - B 0‖ < η * ρ := by
    rw [pi_norm_lt_iff hηρ]
    intro r
    simpa [toR, Real.norm_eq_abs] using hQ0 r
  -- moves
  set a : Fin q → ℚ := fun h => ρ * β' h / N with hadef
  have hapos : ∀ h, 0 < a h := fun h => by
    simp only [hadef]; have := hβ'pos h; positivity
  set mv : ℕ → Ranking m → ℚ := fun l => if hl : l < q then a ⟨l, hl⟩ • û ⟨l, hl⟩ else 0
    with hmvdef
  have hmv_fin : ∀ h : Fin q, mv h = a h • û h := fun h => by simp [hmvdef, h.isLt]
  set Pq : ℕ → Ranking m → ℚ := fun h => ∑ l ∈ Finset.range h, mv l with hPqdef
  set Q : ℕ → Ranking m → ℚ := fun k => Q0 + ∑ l ∈ Finset.range k, mv (l % q) with hQdef
  set L : ℕ := N * q with hLdef
  clear_value Q Pq mv
  have hPfull : toR (Pq q) = ((ρ : ℝ) / N) • c' := by
    simp only [hPqdef, toR_sum]
    rw [Finset.sum_range (fun l => toR (mv l))]
    simp only [hmv_fin, toR_smul, hûR, hc'def, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun h _ => ?_
    congr 1
    simp only [hadef]; push_cast; ring
  have hPbound : ∀ h' ≤ q, ‖toR (Pq h')‖ ≤ ρ * (S' / N) := by
    intro h' hh'
    have e : ∑ l ∈ Finset.range q, ‖toR (mv l)‖ = ρ * (S' / N) := by
      rw [Finset.sum_range (fun l => ‖toR (mv l)‖)]
      simp only [hmv_fin, toR_smul, hûR, norm_smul]
      rw [hS'def, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Real.norm_of_nonneg (by exact_mod_cast (hapos h).le)]
      simp only [hadef]; push_cast; ring
    calc ‖toR (Pq h')‖ = ‖∑ l ∈ Finset.range h', toR (mv l)‖ := by rw [hPqdef, toR_sum]
      _ ≤ ∑ l ∈ Finset.range h', ‖toR (mv l)‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.range q, ‖toR (mv l)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hh')
            (fun _ _ _ => norm_nonneg _)
      _ = _ := e
  have hQform : ∀ n h', h' ≤ q →
      toR (Q (n * q + h')) = toR Q0 + ((n : ℝ) * ((ρ : ℝ) / N)) • c' + toR (Pq h') := by
    intro n h' hh'
    rw [hQdef]; beta_reduce
    rw [sum_range_mod mv q n h' hh',
      show (∑ l ∈ Finset.range q, mv l) = Pq q by rw [hPqdef],
      show (∑ l ∈ Finset.range h', mv l) = Pq h' by rw [hPqdef], toR_add, toR_add, toR_nsmul,
      hPfull, smul_smul, add_assoc]
  have hclose_core : ∀ n h', n ≤ N → h' ≤ q →
      ‖toR (Q (n * q + h')) - B ((n : ℝ) / N)‖ < 4 * (η * ρ) := by
    intro n h' hn hh'
    have ht0 : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
    have ht1 : (n : ℝ) / N ≤ 1 := by
      rw [div_le_one hNpos]; exact_mod_cast hn
    have hdecomp : toR (Q (n * q + h')) - B ((n : ℝ) / N) =
        (toR Q0 - B 0) + (((n : ℝ) / N) * ρ) • (c' - w) + toR (Pq h') - R ((n : ℝ) / N) := by
      rw [hQform n h' hh', hBexp ((n : ℝ) / N)]
      have : (n : ℝ) * ((ρ : ℝ) / N) = ((n : ℝ) / N) * ρ := by ring
      rw [this]
      module
    rw [hdecomp]
    have h1 : ‖(((n : ℝ) / N) * ρ) • (c' - w)‖ < η * ρ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (n : ℝ) / N * ρ * ‖c' - w‖ ≤ 1 * ρ * ‖c' - w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht1 hρ0.le) (norm_nonneg _)
        _ < η * ρ := by
            have := mul_lt_mul_of_pos_left hc' hρ0
            linarith
    have h2 : ‖toR (Pq h')‖ < η * ρ := by
      calc ‖toR (Pq h')‖ ≤ ρ * (S' / N) := hPbound h' hh'
        _ < ρ * η := mul_lt_mul_of_pos_left hNS hρ0
        _ = η * ρ := by ring
    have h3 := hRbound ((n : ℝ) / N) ⟨ht0, ht1⟩
    calc ‖(toR Q0 - B 0) + (((n : ℝ) / N) * ρ) • (c' - w) + toR (Pq h') - R ((n : ℝ) / N)‖
        ≤ ‖toR Q0 - B 0‖ + ‖(((n : ℝ) / N) * ρ) • (c' - w)‖ + ‖toR (Pq h')‖
            + ‖R ((n : ℝ) / N)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ < 4 * (η * ρ) := by linarith
  have hclose : ∀ k ≤ L, ∃ t ∈ Set.Icc (0 : ℝ) 1, ‖toR (Q k) - B t‖ < 4 * (η * ρ) := by
    intro k hk
    rcases Nat.eq_zero_or_pos q with hq | hq
    · have hk0 : k = 0 := by simp [hLdef, hq] at hk; exact hk
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have := hclose_core 0 0 (Nat.zero_le _) (Nat.zero_le _)
      simpa [hk0] using this
    · have hkq : k = (k / q) * q + k % q := by
        have := Nat.div_add_mod k q; rw [mul_comm] at this; exact this.symm
      have hn : k / q ≤ N := Nat.div_le_of_le_mul (by rw [mul_comm]; exact hk)
      refine ⟨((k / q : ℕ) : ℝ) / N, ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_le_one hNpos]; exact_mod_cast hn
      · have := hclose_core (k / q) (k % q) hn (Nat.mod_lt _ hq).le
        rwa [← hkq] at this
  have hε4 : ((ρ : ℝ) / (4 * κ)) / 4 = 4 * (η * ρ) := by
    rw [hηdef]; field_simp; ring
  have hεhalf : (ρ : ℝ) / (4 * κ) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hBlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r, 1 - (ρ : ℝ) / (4 * κ) < B t r := by
    intro t ht r
    have hG := hpos _ (hseg t ht) r
    have h1 := unitVec_nonneg (ell i) r
    have h2 := unitVec_nonneg (ell j) r
    have h3 : 0 ≤ (ρ : ℝ) * ((1 - t) * unitVec (ell i) r + t * unitVec (ell j) r) := by
      have h1t : 0 ≤ 1 - t := by linarith [ht.2]
      exact mul_nonneg hρ0.le (add_nonneg (mul_nonneg h1t h1) (mul_nonneg ht.1 h2))
    simp only [hBdef, referenceCurve, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  refine ⟨ρ, L, Q, hρpos, hεhalf, hseg, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨t, ht, h⟩ := hclose k hk
    exact ⟨t, ht, by rw [hε4, ← hBdef]; exact h⟩
  · have := hclose_core 0 0 (Nat.zero_le _) (Nat.zero_le _)
    rw [hε4, ← hBdef]
    rw [zero_mul, add_zero, Nat.cast_zero, zero_div] at this
    exact this
  · have := hclose_core N 0 le_rfl (Nat.zero_le _)
    rw [hε4, ← hBdef]
    rw [add_zero, div_self hNpos.ne'] at this
    exact this
  · intro k hk
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with hq | hq
      · simp [hLdef, hq] at hk
      · exact hq
    set h : Fin q := ⟨k % q, Nat.mod_lt _ hq⟩ with hhdef
    have hstep : Q (k + 1) = Q k + a h • û h := by
      simp only [hQdef, Finset.sum_range_succ, add_assoc]
      rw [← hmv_fin h]
    rw [hstep]
    apply hûT h (Q k) (a h) (hapos h)
    intro r
    obtain ⟨t, ht, hcl⟩ := hclose k hk.le
    have hr : |(Q k r : ℝ) - B t r| < 4 * (η * ρ) := by
      have := (norm_le_pi_norm (toR (Q k) - B t) r).trans_lt hcl
      simpa [toR, Real.norm_eq_abs] using this
    have hBt := hBlow t ht r
    rw [← hε4] at hr
    have hQr : (3 / 8 : ℝ) < Q k r := by
      rw [abs_lt] at hr; linarith
    have haR : ((a h * ((K : ℚ) + 1) : ℚ) : ℝ) ≤ 1 / 4 := by
      have hb := hBs h
      have hbR : ((β' h : ℚ) : ℝ) ≤ Bs := by exact_mod_cast hb
      have hb0 : (0 : ℝ) ≤ β' h := by exact_mod_cast (hβ'pos h).le
      have hBs0R : (0 : ℝ) ≤ Bs := by exact_mod_cast hBs0
      have h4 : (ρ : ℝ) * (4 * lamR * ((Bs : ℝ) + 1)) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at hρ_4
      simp only [hadef]
      push_cast
      have h5 : (ρ : ℝ) * β' h / N ≤ ρ * β' h := by
        rw [div_le_iff₀ hNpos]
        exact le_mul_of_one_le_right (mul_nonneg hρ0.le hb0) hN1
      have h6 : (ρ : ℝ) * β' h ≤ ρ * Bs := mul_le_mul_of_nonneg_left hbR hρ0.le
      have hl0 : (0:ℝ) ≤ (K : ℝ) + 1 := by positivity
      have hpl : (0:ℝ) ≤ ρ * lamR := mul_nonneg hρ0.le (zero_le_one.trans hlam)
      have h7 : (ρ : ℝ) * Bs * lamR * 4 ≤ ρ * (4 * lamR * (Bs + 1)) := by
        have : (ρ : ℝ) * (4 * lamR * (Bs + 1)) = ρ * Bs * lamR * 4 + 4 * (ρ * lamR) := by ring
        rw [this]; linarith
      calc (ρ : ℝ) * β' h / N * ((K : ℝ) + 1) ≤ ρ * Bs * lamR := by
            rw [hlamR]; exact mul_le_mul_of_nonneg_right (h5.trans h6) hl0
        _ ≤ 1 / 4 := by linarith
    have : ((a h * ((K : ℚ) + 1) : ℚ) : ℝ) ≤ (Q k r : ℝ) := by linarith
    exact_mod_cast this
