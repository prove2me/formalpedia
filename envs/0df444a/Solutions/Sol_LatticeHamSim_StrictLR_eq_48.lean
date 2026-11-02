-- Prove2me | solution 1 for LatticeHamSim.StrictLR.eq_48
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:51:52.740201+00:00
-- url     : https://prove2.me/submissions/8519eeb9-4473-4a86-9307-23a9be6cb78b

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
import Theorems.Thm_LatticeHamSim_StrictLR_eq_44
import Theorems.Thm_LatticeHamSim_StrictLR_eq_45
import Theorems.Thm_LatticeHamSim_StrictLR_eq_46
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Aux_LHS_48

open LatticeHamSim.CommLR LatticeHamSim.StrictLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

lemma comm_bound (P B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖P * B - B * P‖ ≤ 2 * ‖P‖ * ‖B‖ := by
  calc ‖P * B - B * P‖ ≤ ‖P * B‖ + ‖B * P‖ := norm_sub_le _ _
    _ ≤ ‖P‖ * ‖B‖ + ‖B‖ * ‖P‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖B‖ := by ring

lemma evolve_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (t : ℝ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖evolve (H h) t O‖ = ‖O‖ := by
  have hsa : star (H h) = H h := by
    unfold H
    rw [star_sum]
    exact Finset.sum_congr rfl (fun X _ => hherm X)
  have key : ∀ s : ℝ, NormedSpace.exp ((Complex.I * (s : ℂ)) • H h) ∈
      unitary (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
    intro s
    have hs : ((s : ℂ) • H h) ∈ selfAdjoint (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
    have := (selfAdjoint.expUnitary ⟨(s : ℂ) • H h, hs⟩).prop
    simp only [selfAdjoint.expUnitary_coe, smul_smul] at this
    exact this
  unfold evolve
  have hU := key t
  have hV := key (-t)
  rw [show (-(Complex.I * (t : ℂ))) = Complex.I * ((-t : ℝ) : ℂ) by push_cast; ring]
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

lemma supportedOn_smul (X : Finset Λ) (c : ℂ) (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : SupportedOn X A) : SupportedOn X (c • A) := by
  obtain ⟨m, hm⟩ := hA
  refine ⟨c • m, fun σ τ => ?_⟩
  simp only [Matrix.smul_apply, hm σ τ, smul_eq_mul, mul_ite, mul_zero]

lemma cb_bddAbove (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    BddAbove {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖} := by
  refine ⟨2 * ‖B‖, ?_⟩
  rintro r ⟨A, -, hA1, rfl⟩
  refine le_trans (comm_bound _ _) ?_
  rw [evolve_norm h hherm]
  nlinarith [norm_nonneg A, norm_nonneg B]

lemma norm_comm_evolve_le_CB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ)
    (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hA : SupportedOn X A) :
    ‖evolve (H h) t A * B - B * evolve (H h) t A‖ ≤ ‖A‖ * CB h B X t := by
  by_cases hA0 : ‖A‖ = 0
  · have hAz : A = 0 := norm_eq_zero.mp hA0
    simp [hAz, hA0, evolve]
  · have hApos : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg A) (Ne.symm hA0)
    set c : ℂ := ((‖A‖⁻¹ : ℝ) : ℂ)
    set A' : Matrix (Λ → Fin q) (Λ → Fin q) ℂ := c • A
    have hA'supp : SupportedOn X A' := supportedOn_smul X c A hA
    have hA'norm : ‖A'‖ ≤ 1 := by
      change ‖((‖A‖⁻¹ : ℝ) : ℂ) • A‖ ≤ 1
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hApos)),
        inv_mul_cancel₀ hA0]
    have hev : evolve (H h) t A' * B - B * evolve (H h) t A' =
        c • (evolve (H h) t A * B - B * evolve (H h) t A) := by
      unfold A' evolve
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have hmem : ‖A‖⁻¹ * ‖evolve (H h) t A * B - B * evolve (H h) t A‖ ∈
        {r : ℝ | ∃ M : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
          SupportedOn X M ∧ ‖M‖ ≤ 1 ∧
          r = ‖evolve (H h) t M * B - B * evolve (H h) t M‖} := by
      refine ⟨A', hA'supp, hA'norm, ?_⟩
      rw [hev, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hApos))]
    have hle : ‖A‖⁻¹ * ‖evolve (H h) t A * B - B * evolve (H h) t A‖ ≤ CB h B X t :=
      le_csSup (cb_bddAbove h hherm B X t) hmem
    calc ‖evolve (H h) t A * B - B * evolve (H h) t A‖
        = ‖A‖ * (‖A‖⁻¹ * ‖evolve (H h) t A * B - B * evolve (H h) t A‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hA0, one_mul]
      _ ≤ ‖A‖ * CB h B X t := mul_le_mul_of_nonneg_left hle (le_of_lt hApos)

lemma supportedOn_empty_eq_smul_one (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : SupportedOn ∅ A) :
    ∃ c : ℂ, A = c • (1 : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
  obtain ⟨m, hm⟩ := hA
  let f₀ : (∅ : Finset Λ) → Fin q := fun x => False.elim (Finset.notMem_empty x.1 x.2)
  refine ⟨m f₀ f₀, ?_⟩
  ext σ τ
  rw [hm σ τ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_boole]
  have hcond : (∀ x, x ∉ (∅ : Finset Λ) → σ x = τ x) ↔ σ = τ := by
    simp [funext_iff]
  have hfσ : (fun x : (∅ : Finset Λ) => σ x.1) = f₀ := by
    funext x; exact False.elim (Finset.notMem_empty x.1 x.2)
  have hfτ : (fun x : (∅ : Finset Λ) => τ x.1) = f₀ := by
    funext x; exact False.elim (Finset.notMem_empty x.1 x.2)
  rw [hfσ, hfτ]
  by_cases hστ : σ = τ
  · rw [if_pos (hcond.mpr hστ), if_pos hστ]
  · rw [if_neg (mt hcond.mp hστ), if_neg hστ]

lemma comm_evolve_supportedOn_empty (J A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (t : ℝ) (hA : SupportedOn ∅ A) :
    evolve J t A * B - B * evolve J t A = 0 := by
  obtain ⟨c, rfl⟩ := supportedOn_empty_eq_smul_one A hA
  haveI : NormedAlgebra ℚ (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hexp : NormedSpace.exp ((Complex.I * (t : ℂ)) • J) *
      NormedSpace.exp ((-(Complex.I * (t : ℂ))) • J) = 1 := by
    rw [neg_smul, ← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl _)),
      add_neg_cancel, NormedSpace.exp_zero]
  have hev : evolve J t (c • 1) = c • 1 := by
    unfold evolve
    rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, hexp]
  rw [hev, Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one, sub_self]

lemma linked_cons_iff {k : ℕ} (P Q : Finset Λ) (Z' : Fin k → Finset Λ) :
    Linked P (Fin.cons Q Z') ↔ meets P Q ∧ Linked Q Z' := by
  unfold Linked
  rw [Fin.forall_fin_succ]
  apply and_congr
  · rfl
  · refine forall_congr' (fun j => ?_)
    have hch : chain P (Fin.cons Q Z') j.succ.castSucc = chain Q Z' j.castSucc := by
      unfold chain
      rw [Fin.castSucc_succ, Fin.cons_succ]
    rw [hch, Fin.cons_succ]

lemma linkedSum_succ (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (P : Finset Λ) (k : ℕ) :
    linkedSum h P (k + 1) =
      ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q), ‖h Q‖ * linkedSum h Q k := by
  unfold linkedSum
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Finset Λ)), Fintype.sum_prod_type]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  split_ifs with hPQ
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Z' _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.consEquiv_apply, Prod.fst, Prod.snd, Fin.cons_zero, Fin.cons_succ]
    have hiff := linked_cons_iff P Q Z'
    split_ifs with h1 h2 h2
    · ring
    · exfalso; exact h2 (hiff.mp h1).2
    · exfalso; exact h1 (hiff.mpr ⟨hPQ, h2⟩)
    · ring
  · refine Finset.sum_eq_zero (fun Z' _ => ?_)
    simp only [Fin.consEquiv_apply, Prod.fst, Prod.snd]
    have hiff := linked_cons_iff P Q Z'
    split_ifs with h1
    · exfalso; exact hPQ (hiff.mp h1).1
    · ring

lemma linkedSum_zero (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (P : Finset Λ) :
    linkedSum h P 0 = 1 := by
  unfold linkedSum
  rw [Finset.univ_unique, Finset.sum_singleton]
  have hL : ∀ f : Fin 0 → Finset Λ, Linked P f := fun _ j => Fin.elim0 j
  split_ifs with h1
  · simp
  · exfalso; exact h1 (hL _)

lemma linkedSum_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (ζ₀ : ℝ) (hζ₀ : ∀ x : Λ, ∑ Q ∈ Finset.univ.filter (fun Q => x ∈ Q), (Q.card : ℝ) * ‖h Q‖ ≤ ζ₀)
    (hζ₀_nn : 0 ≤ ζ₀) :
    ∀ (k : ℕ) (P : Finset Λ), P.Nonempty → linkedSum h P k ≤ (P.card : ℝ) * ζ₀ ^ k
  | 0, P, hP => by
    rw [linkedSum_zero, pow_zero, mul_one]
    exact_mod_cast hP.card_pos
  | k + 1, P, hP => by
    rw [linkedSum_succ]
    have hstep1 : ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q), ‖h Q‖ * linkedSum h Q k ≤
        ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q), ‖h Q‖ * ((Q.card : ℝ) * ζ₀ ^ k) := by
      refine Finset.sum_le_sum (fun Q hQ => ?_)
      have hQne : Q.Nonempty := by
        obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hQ).2
        exact ⟨x, (Finset.mem_inter.mp hx).2⟩
      exact mul_le_mul_of_nonneg_left (linkedSum_le h hloc ζ₀ hζ₀ hζ₀_nn k Q hQne) (norm_nonneg _)
    have hstep2 : ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q), ‖h Q‖ * ((Q.card : ℝ) * ζ₀ ^ k) =
        ζ₀ ^ k * ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q),
          (Q.card : ℝ) * ‖h Q‖ * (if setDist Q ∅ ≤ 0 then 1 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      have hsd : setDist Q (∅ : Finset Λ) ≤ 0 := by
        unfold setDist
        simp
      rw [if_pos hsd]
      ring
    have hstep3 := eq_46 h hloc ζ₀ hζ₀ P ∅ 0
    have hstep4 : ζ₀ * ∑ p ∈ P, (if Metric.infDist p ((∅ : Finset Λ) : Set Λ) ≤ 0 + 1 then (1 : ℝ) else 0) =
        ζ₀ * (P.card : ℝ) := by
      congr 1
      calc ∑ p ∈ P, (if Metric.infDist p ((∅ : Finset Λ) : Set Λ) ≤ 0 + 1 then (1 : ℝ) else 0)
          = ∑ p ∈ P, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun p _ => ?_)
            simp [Metric.infDist_empty]
        _ = (P.card : ℝ) := by simp
    rw [hstep4] at hstep3
    calc ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q), ‖h Q‖ * linkedSum h Q k
        ≤ ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q), ‖h Q‖ * ((Q.card : ℝ) * ζ₀ ^ k) := hstep1
      _ = ζ₀ ^ k * ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q),
            (Q.card : ℝ) * ‖h Q‖ * (if setDist Q ∅ ≤ 0 then 1 else 0) := hstep2
      _ ≤ ζ₀ ^ k * (ζ₀ * (P.card : ℝ)) := mul_le_mul_of_nonneg_left hstep3 (pow_nonneg hζ₀_nn k)
      _ = (P.card : ℝ) * ζ₀ ^ (k + 1) := by ring

end Aux_LHS_48

open LatticeHamSim.CommLR LatticeHamSim.StrictLR Aux_LHS_48 in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (ζ₀ : ℝ) (hζ₀ : ∀ x : Λ, ∑ Q ∈ Finset.univ.filter (fun Q => x ∈ Q), (Q.card : ℝ) * ‖h Q‖ ≤ ζ₀)
    (X Y : Finset Λ) (A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : LatticeHamSim.CommLR.SupportedOn X A) (hB : LatticeHamSim.CommLR.SupportedOn Y B) (t : ℝ) :
    ‖LatticeHamSim.CommLR.evolve (LatticeHamSim.CommLR.H h) t A * B - B * LatticeHamSim.CommLR.evolve (LatticeHamSim.CommLR.H h) t A‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card * (2 * ζ₀ * |t|) ^ ⌊LatticeHamSim.CommLR.setDist X Y⌋₊ /
        (⌊LatticeHamSim.CommLR.setDist X Y⌋₊).factorial := by
  by_cases hX : X.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hX
    have hζ₀_nn : 0 ≤ ζ₀ := by
      refine le_trans ?_ (hζ₀ x₀)
      exact Finset.sum_nonneg (fun Q _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    set ℓ := ⌊setDist X Y⌋₊
    have h1 := norm_comm_evolve_le_CB h hherm B X t A hA
    have h2 := eq_44 h hherm hsupp hloc B X Y hB t
    have h3 := linkedSum_le h hloc ζ₀ hζ₀ hζ₀_nn ℓ X ⟨x₀, hx₀⟩
    have hfac_pos : (0 : ℝ) ≤ (ℓ.factorial : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ 2 * ‖B‖ * (2 * |t|) ^ ℓ / (ℓ.factorial : ℝ) := by positivity
    calc ‖evolve (H h) t A * B - B * evolve (H h) t A‖
        ≤ ‖A‖ * CB h B X t := h1
      _ ≤ ‖A‖ * (2 * ‖B‖ * (2 * |t|) ^ ℓ / (ℓ.factorial : ℝ) * linkedSum h X ℓ) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg A)
      _ ≤ ‖A‖ * (2 * ‖B‖ * (2 * |t|) ^ ℓ / (ℓ.factorial : ℝ) * ((X.card : ℝ) * ζ₀ ^ ℓ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hcoeff_nn) (norm_nonneg A)
      _ = 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) * ((2 * |t|) * ζ₀) ^ ℓ / (ℓ.factorial : ℝ) := by
          rw [mul_pow]; ring
      _ = 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) * (2 * ζ₀ * |t|) ^ ℓ / (ℓ.factorial : ℝ) := by ring
  · have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    subst hXe
    rw [comm_evolve_supportedOn_empty (H h) A B t hA, norm_zero, Finset.card_empty, Nat.cast_zero]
    ring_nf
    exact le_rfl
