-- Prove2me | solution 1 for LatticeHamSim.CommLR.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:32:31.147272+00:00
-- url     : https://prove2.me/submissions/714700ea-d0e0-4e4e-b117-001f666be8a8

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace Aux_LHS_CommLR_27

open LatticeHamSim.CommLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

noncomputable local instance : NormedAlgebra ℝ (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

noncomputable local instance : NormedAlgebra ℚ (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

lemma comm_disjoint (A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z Y : Finset Λ)
    (hA : SupportedOn Z A) (hB : SupportedOn Y B) (hd : Disjoint Z Y) : A * B = B * A := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hZY : ∀ x, x ∈ Z → x ∉ Y := fun x hx hy => Finset.disjoint_left.mp hd hx hy
  ext σ ρ
  simp only [Matrix.mul_apply, ha, hb]
  set τ1 : Λ → Fin q := fun x => if x ∈ Z then ρ x else σ x with hτ1
  set τ2 : Λ → Fin q := fun x => if x ∈ Y then ρ x else σ x with hτ2
  rw [Finset.sum_eq_single τ1, Finset.sum_eq_single τ2]
  · by_cases hC : ∀ x, x ∉ Y → x ∉ Z → σ x = ρ x
    · have p1 : ∀ x, x ∉ Z → σ x = τ1 x := fun x hx => by simp [τ1, hx]
      have p2 : ∀ x, x ∉ Y → τ1 x = ρ x := fun x hx => by
        by_cases hz : x ∈ Z
        · simp [τ1, hz]
        · simp only [τ1, hz, if_false]; exact hC x hx hz
      have p3 : ∀ x, x ∉ Y → σ x = τ2 x := fun x hx => by simp [τ2, hx]
      have p4 : ∀ x, x ∉ Z → τ2 x = ρ x := fun x hx => by
        by_cases hy : x ∈ Y
        · simp [τ2, hy]
        · simp only [τ2, hy, if_false]; exact hC x hy hx
      rw [if_pos p1, if_pos p2, if_pos p3, if_pos p4]
      have e1 : (fun x : Z => τ1 x) = (fun x : Z => ρ x) := by
        funext x; simp [τ1, x.2]
      have e2 : (fun x : Y => τ1 x) = (fun x : Y => σ x) := by
        funext x
        have hx : (x : Λ) ∉ Z := fun h => hZY x h x.2
        simp only [τ1, hx, if_false]
      have e3 : (fun x : Y => τ2 x) = (fun x : Y => ρ x) := by
        funext x; simp [τ2, x.2]
      have e4 : (fun x : Z => τ2 x) = (fun x : Z => σ x) := by
        funext x; simp [τ2, hZY x x.2]
      rw [e1, e2, e3, e4, mul_comm]
    · push_neg at hC
      obtain ⟨x, hxY, hxZ, hne⟩ := hC
      have n1 : ¬ ∀ x, x ∉ Y → τ1 x = ρ x := fun h => hne (by
        have := h x hxY; simpa [τ1, hxZ] using this)
      have n2 : ¬ ∀ x, x ∉ Z → τ2 x = ρ x := fun h => hne (by
        have := h x hxZ; simpa [τ2, hxY] using this)
      rw [if_neg n1, if_neg n2, mul_zero, mul_zero]
  · intro τ _ hne
    by_cases h1 : ∀ x, x ∉ Y → σ x = τ x
    · by_cases h2 : ∀ x, x ∉ Z → τ x = ρ x
      · exfalso; apply hne; funext x
        by_cases hx : x ∈ Y
        · simp only [τ2, hx, if_true]
          exact h2 x (fun hz => hZY x hz hx)
        · simp only [τ2, hx, if_false]; exact (h1 x hx).symm
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro τ _ hne
    by_cases h1 : ∀ x, x ∉ Z → σ x = τ x
    · by_cases h2 : ∀ x, x ∉ Y → τ x = ρ x
      · exfalso; apply hne; funext x
        by_cases hx : x ∈ Z
        · simp only [τ1, hx, if_true]
          exact h2 x (hZY x hx)
        · simp only [τ1, hx, if_false]; exact (h1 x hx).symm
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma supportedOn_mono {W V : Finset Λ} (hWV : W ⊆ V)
    {A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ} (hA : SupportedOn W A) :
    SupportedOn V A := by
  classical
  obtain ⟨a, ha⟩ := hA
  refine ⟨fun σV τV =>
    if (∀ v : V, (v : Λ) ∉ W → σV v = τV v)
    then a (fun w : W => σV ⟨w.1, hWV w.2⟩) (fun w : W => τV ⟨w.1, hWV w.2⟩)
    else 0, fun σ τ => ?_⟩
  rw [ha σ τ]
  by_cases hV : ∀ x, x ∉ V → σ x = τ x
  · rw [if_pos hV]
    have hiff : (∀ x, x ∉ W → σ x = τ x) ↔ (∀ v : V, (v : Λ) ∉ W → σ v = τ v) := by
      constructor
      · intro hW v hv; exact hW v.1 hv
      · intro hVW x hxW
        by_cases hxV : x ∈ V
        · exact hVW ⟨x, hxV⟩ hxW
        · exact hV x hxV
    by_cases hW : ∀ x, x ∉ W → σ x = τ x
    · rw [if_pos hW]
      dsimp only
      rw [if_pos (hiff.mp hW)]
    · rw [if_neg hW]
      dsimp only
      rw [if_neg (mt hiff.mpr hW)]
  · rw [if_neg hV]
    have hW : ¬ ∀ x, x ∉ W → σ x = τ x := by
      intro hW
      apply hV
      intro x hxV
      exact hW x (fun hxW => hxV (hWV hxW))
    rw [if_neg hW]

lemma supportedOn_sub {W : Finset Λ}
    {A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ} (hA : SupportedOn W A) (hB : SupportedOn W B) :
    SupportedOn W (A - B) := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨a - b, fun σ τ => ?_⟩
  simp only [Matrix.sub_apply, ha, hb]
  split_ifs <;> ring

lemma supportedOn_mul {W : Finset Λ}
    {A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ} (hA : SupportedOn W A) (hB : SupportedOn W B) :
    SupportedOn W (A * B) := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨a * b, fun σ τ => ?_⟩
  simp only [Matrix.mul_apply, ha, hb]
  by_cases hW : ∀ x, x ∉ W → σ x = τ x
  · rw [if_pos hW]
    let extW : (W → Fin q) → (Λ → Fin q) :=
      fun ρW x => if hx : x ∈ W then ρW ⟨x, hx⟩ else σ x
    have h1 : ∀ ρW : W → Fin q,
        a (fun x => σ x) ρW * b ρW (fun x => τ x) =
        ∑ ρ : Λ → Fin q, if ρ = extW ρW then a (fun x => σ x) ρW * b ρW (fun x => τ x) else 0 := by
      intro ρW
      rw [Finset.sum_eq_single (extW ρW)]
      · simp
      · intro ρ _ hne; exact if_neg hne
      · intro h; exact absurd (Finset.mem_univ _) h
    calc ∑ ρ : Λ → Fin q,
          (if ∀ x, x ∉ W → σ x = ρ x then a (fun x => σ x) (fun x => ρ x) else 0) *
          (if ∀ x, x ∉ W → ρ x = τ x then b (fun x => ρ x) (fun x => τ x) else 0)
        = ∑ ρ : Λ → Fin q, ∑ ρW : W → Fin q,
            if ρ = extW ρW then a (fun x => σ x) ρW * b ρW (fun x => τ x) else 0 := by
          refine Finset.sum_congr rfl (fun ρ _ => ?_)
          rw [Finset.sum_eq_single (fun w : W => ρ w.1)]
          · by_cases hσρ : ∀ x, x ∉ W → σ x = ρ x
            · have hρτ : ∀ x, x ∉ W → ρ x = τ x := fun x hx => (hσρ x hx).symm.trans (hW x hx)
              have hext : ρ = extW (fun w : W => ρ w.1) := by
                funext x
                by_cases hx : x ∈ W
                · simp [extW, hx]
                · simp [extW, hx, (hσρ x hx).symm]
              rw [if_pos hσρ, if_pos hρτ, if_pos hext]
            · have hne : ρ ≠ extW (fun w : W => ρ w.1) := by
                intro heq
                apply hσρ
                intro x hx
                have := congr_fun heq x
                simpa [extW, hx] using this.symm
              rw [if_neg hσρ, zero_mul, if_neg hne]
          · intro ρW _ hne
            have hne' : ρ ≠ extW ρW := by
              intro heq
              apply hne
              funext w
              have := congr_fun heq w.1
              simpa [extW, w.2] using this.symm
            exact if_neg hne'
          · intro h; exact absurd (Finset.mem_univ _) h
      _ = ∑ ρW : W → Fin q, ∑ ρ : Λ → Fin q,
            if ρ = extW ρW then a (fun x => σ x) ρW * b ρW (fun x => τ x) else 0 :=
          Finset.sum_comm
      _ = ∑ ρW : W → Fin q, a (fun x => σ x) ρW * b ρW (fun x => τ x) := by
          refine Finset.sum_congr rfl (fun ρW _ => (h1 ρW).symm)
  · rw [if_neg hW]
    refine Finset.sum_eq_zero (fun ρ _ => ?_)
    by_cases h1 : ∀ x, x ∉ W → σ x = ρ x
    · have h2 : ¬ ∀ x, x ∉ W → ρ x = τ x := by
        intro h2
        apply hW
        intro x hx
        exact (h1 x hx).trans (h2 x hx)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma supportedOn_smul (X : Finset Λ) (c : ℂ) (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : SupportedOn X A) : SupportedOn X (c • A) := by
  obtain ⟨m, hm⟩ := hA
  refine ⟨c • m, fun σ τ => ?_⟩
  simp only [Matrix.smul_apply, hm σ τ, smul_eq_mul, mul_ite, mul_zero]

lemma comm_bound (P B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖P * B - B * P‖ ≤ 2 * ‖P‖ * ‖B‖ := by
  calc ‖P * B - B * P‖ ≤ ‖P * B‖ + ‖B * P‖ := norm_sub_le _ _
    _ ≤ ‖P‖ * ‖B‖ + ‖B‖ * ‖P‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖B‖ := by ring

lemma evolve_norm_of_isHermitian (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hJ : J.IsHermitian) (t : ℝ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖evolve J t O‖ = ‖O‖ := by
  have hsa : star J = J := hJ
  have key : ∀ s : ℝ, NormedSpace.exp ((Complex.I * (s : ℂ)) • J) ∈
      unitary (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
    intro s
    have hs : ((s : ℂ) • J) ∈ selfAdjoint (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
    have := (selfAdjoint.expUnitary ⟨(s : ℂ) • J, hs⟩).prop
    simp only [selfAdjoint.expUnitary_coe, smul_smul] at this
    exact this
  unfold evolve
  have hU := key t
  have hV := key (-t)
  rw [show (-(Complex.I * (t : ℂ))) = Complex.I * ((-t : ℝ) : ℂ) by push_cast; ring]
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

lemma H_isHermitian (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) : (H h).IsHermitian := by
  change star (H h) = H h
  unfold H
  rw [star_sum]
  exact Finset.sum_congr rfl (fun X _ => hherm X)

lemma evolve_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (t : ℝ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖evolve (H h) t O‖ = ‖O‖ :=
  evolve_norm_of_isHermitian (H h) (H_isHermitian h hherm) t O

lemma exp_neg_mul_exp (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (s : ℝ) :
    NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) *
      NormedSpace.exp ((Complex.I * (s : ℂ)) • J) = 1 := by
  rw [neg_smul, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)),
    neg_add_cancel, NormedSpace.exp_zero]

lemma exp_mul_exp_neg (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (s : ℝ) :
    NormedSpace.exp ((Complex.I * (s : ℂ)) • J) *
      NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) = 1 := by
  rw [neg_smul, ← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl _)),
    add_neg_cancel, NormedSpace.exp_zero]

lemma evolve_zero (J O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) : evolve J 0 O = O := by
  simp [evolve]

lemma evolve_mul (J M N : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (s : ℝ) :
    evolve J s (M * N) = evolve J s M * evolve J s N := by
  unfold evolve
  calc NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * (M * N) *
        NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)
      = NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * M *
        (NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) *
          NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) *
        N * NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) := by
        rw [exp_neg_mul_exp]; noncomm_ring
    _ = (NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * M *
          NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) *
        (NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * N *
          NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) := by
        noncomm_ring

lemma evolve_sub (J M N : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (s : ℝ) :
    evolve J s (M - N) = evolve J s M - evolve J s N := by
  unfold evolve
  noncomm_ring

lemma evolve_sum {ι : Type*} (S : Finset ι) (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (s : ℝ) (F : ι → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    evolve J s (∑ i ∈ S, F i) = ∑ i ∈ S, evolve J s (F i) := by
  unfold evolve
  rw [Finset.mul_sum, Finset.sum_mul]

lemma evolve_self (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (s : ℝ) :
    evolve J s J = J := by
  unfold evolve
  have hcomm : J * NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) =
      NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) * J :=
    (Commute.refl J |>.smul_right (-(Complex.I * (s : ℂ)))).exp_right
  rw [mul_assoc, hcomm, ← mul_assoc, exp_mul_exp_neg, one_mul]

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

lemma cb_set_nonempty (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖}.Nonempty := by
  refine ⟨0, 0, ⟨0, fun σ τ => by simp⟩, by simp, ?_⟩
  simp [evolve]

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

lemma cb_nonneg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    0 ≤ CB h B X t := by
  unfold CB
  refine le_csSup (cb_bddAbove h hherm B X t) ⟨0, ⟨0, fun σ τ => by simp⟩, by simp, ?_⟩
  simp [evolve]

lemma continuous_exp_line (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (c : ℂ) :
    Continuous (fun s : ℝ => NormedSpace.exp ((c * (s : ℂ)) • J)) := by
  exact NormedSpace.exp_continuous.comp ((continuous_const.mul Complex.continuous_ofReal).smul continuous_const)

lemma continuous_evolve (J A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    Continuous (fun s : ℝ => evolve J s A) := by
  unfold evolve
  have h1 : Continuous (fun s : ℝ => NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) :=
    continuous_exp_line J Complex.I
  have h2 : Continuous (fun s : ℝ => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) := by
    have : (fun s : ℝ => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) =
        (fun s : ℝ => NormedSpace.exp (((-Complex.I) * (s : ℂ)) • J)) := by
      ext s; rw [neg_mul]
    rw [this]
    exact continuous_exp_line J (-Complex.I)
  exact (h1.mul continuous_const).mul h2

lemma cb_sub_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) (s₁ s₂ : ℝ) :
    CB h B Z s₁ - CB h B Z s₂ ≤
      2 * ‖B‖ * (‖NormedSpace.exp ((Complex.I * (s₁ : ℂ)) • H h) -
          NormedSpace.exp ((Complex.I * (s₂ : ℂ)) • H h)‖ *
        ‖NormedSpace.exp ((-(Complex.I * (s₁ : ℂ))) • H h)‖ +
        ‖NormedSpace.exp ((Complex.I * (s₂ : ℂ)) • H h)‖ *
        ‖NormedSpace.exp ((-(Complex.I * (s₁ : ℂ))) • H h) -
          NormedSpace.exp ((-(Complex.I * (s₂ : ℂ))) • H h)‖) := by
  set U : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((Complex.I * (s : ℂ)) • H h)
  set V : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H h)
  set M : ℝ := 2 * ‖B‖ * (‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖)
  rw [sub_le_iff_le_add]
  unfold CB
  refine csSup_le (cb_set_nonempty h B Z s₁) ?_
  rintro r ⟨A, hAsupp, hA1, rfl⟩
  have hmem2 : ‖evolve (H h) s₂ A * B - B * evolve (H h) s₂ A‖ ≤ CB h B Z s₂ :=
    le_csSup (cb_bddAbove h hherm B Z s₂) ⟨A, hAsupp, hA1, rfl⟩
  have hdiff : evolve (H h) s₁ A - evolve (H h) s₂ A =
      (U s₁ - U s₂) * A * V s₁ + U s₂ * A * (V s₁ - V s₂) := by
    unfold evolve U V
    noncomm_ring
  have hev_diff : ‖evolve (H h) s₁ A - evolve (H h) s₂ A‖ ≤
      ‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖ := by
    rw [hdiff]
    calc ‖(U s₁ - U s₂) * A * V s₁ + U s₂ * A * (V s₁ - V s₂)‖
        ≤ ‖(U s₁ - U s₂) * A * V s₁‖ + ‖U s₂ * A * (V s₁ - V s₂)‖ := norm_add_le _ _
      _ ≤ ‖(U s₁ - U s₂) * A‖ * ‖V s₁‖ + ‖U s₂ * A‖ * ‖V s₁ - V s₂‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (‖U s₁ - U s₂‖ * ‖A‖) * ‖V s₁‖ + (‖U s₂‖ * ‖A‖) * ‖V s₁ - V s₂‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖U s₁ - U s₂‖ * 1) * ‖V s₁‖ + (‖U s₂‖ * 1) * ‖V s₁ - V s₂‖ := by
          gcongr
      _ = ‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖ := by ring
  have hcomm_diff : ‖(evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
      (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A)‖ ≤ M := by
    have heq : (evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
        (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A) =
        (evolve (H h) s₁ A - evolve (H h) s₂ A) * B - B * (evolve (H h) s₁ A - evolve (H h) s₂ A) := by
      noncomm_ring
    rw [heq]
    calc ‖(evolve (H h) s₁ A - evolve (H h) s₂ A) * B - B * (evolve (H h) s₁ A - evolve (H h) s₂ A)‖
        ≤ 2 * ‖evolve (H h) s₁ A - evolve (H h) s₂ A‖ * ‖B‖ := comm_bound _ _
      _ ≤ 2 * (‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖) * ‖B‖ := by
          gcongr
      _ = M := by unfold M; ring
  calc ‖evolve (H h) s₁ A * B - B * evolve (H h) s₁ A‖
      ≤ ‖evolve (H h) s₂ A * B - B * evolve (H h) s₂ A‖ +
        ‖(evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
          (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A)‖ := norm_le_insert' _ _
    _ ≤ CB h B Z s₂ + M := add_le_add hmem2 hcomm_diff
    _ = M + CB h B Z s₂ := add_comm _ _

lemma continuous_CB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) :
    Continuous (fun s : ℝ => CB h B Z s) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set U : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((Complex.I * (s : ℂ)) • H h)
  set V : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H h)
  have hU : Continuous U := continuous_exp_line (H h) Complex.I
  have hV : Continuous V := by
    have : V = fun s : ℝ => NormedSpace.exp (((-Complex.I) * (s : ℂ)) • H h) := by
      ext s; unfold V; rw [neg_mul]
    rw [this]
    exact continuous_exp_line (H h) (-Complex.I)
  set F : ℝ → ℝ := fun s =>
    max (2 * ‖B‖ * (‖U s - U s₀‖ * ‖V s‖ + ‖U s₀‖ * ‖V s - V s₀‖))
        (2 * ‖B‖ * (‖U s₀ - U s‖ * ‖V s₀‖ + ‖U s‖ * ‖V s₀ - V s‖))
  have hF_cont : Continuous F := by
    unfold F
    refine Continuous.max ?_ ?_
    · exact continuous_const.mul (((hU.sub continuous_const).norm.mul hV.norm).add
        (continuous_const.mul (hV.sub continuous_const).norm))
    · exact continuous_const.mul (((continuous_const.sub hU).norm.mul continuous_const).add
        (hU.norm.mul (continuous_const.sub hV).norm))
  have hF0 : F s₀ = 0 := by
    unfold F
    simp
  have hFtend : Filter.Tendsto F (nhds s₀) (nhds 0) := by
    rw [← hF0]
    exact hF_cont.continuousAt
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hFtend
  rw [Real.norm_eq_abs, abs_le]
  have h1 : CB h B Z s₀ - CB h B Z s ≤ F s :=
    (cb_sub_le h hherm B Z s₀ s).trans (le_max_right _ _)
  have h2 : CB h B Z s - CB h B Z s₀ ≤ F s :=
    (cb_sub_le h hherm B Z s s₀).trans (le_max_left _ _)
  constructor <;> linarith

lemma hasDerivAt_evolve (J A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => evolve J u A)
      (Complex.I • (J * evolve J s A - evolve J s A * J)) s := by
  have hU_eq : (fun u : ℝ => NormedSpace.exp ((Complex.I * (u : ℂ)) • J)) =
      (fun u : ℝ => NormedSpace.exp (u • (Complex.I • J))) := by
    funext u
    congr 1
    change (Complex.I * (u : ℂ)) • J = (u : ℂ) • (Complex.I • J)
    rw [smul_smul, mul_comm]
  have hV_eq : (fun u : ℝ => NormedSpace.exp ((-(Complex.I * (u : ℂ))) • J)) =
      (fun u : ℝ => NormedSpace.exp (u • ((-Complex.I) • J))) := by
    funext u
    congr 1
    change (-(Complex.I * (u : ℂ))) • J = (u : ℂ) • ((-Complex.I) • J)
    rw [smul_smul, mul_neg, mul_comm]
  have hU : HasDerivAt (fun u : ℝ => NormedSpace.exp ((Complex.I * (u : ℂ)) • J))
      (NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * (Complex.I • J)) s := by
    rw [hU_eq]
    have hd := hasDerivAt_exp_smul_const (Complex.I • J) s
    rwa [← congr_fun hU_eq s] at hd
  have hV : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-(Complex.I * (u : ℂ))) • J))
      (NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) * ((-Complex.I) • J)) s := by
    rw [hV_eq]
    have hd := hasDerivAt_exp_smul_const ((-Complex.I) • J) s
    rwa [← congr_fun hV_eq s] at hd
  have htot : HasDerivAt (fun u : ℝ => evolve J u A)
      (((NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * (Complex.I • J)) * A) *
        NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) +
       (NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * A) *
        (NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) * ((-Complex.I) • J))) s :=
    (hU.mul_const A).mul hV
  have hcomm : NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * J =
      J * NormedSpace.exp ((Complex.I * (s : ℂ)) • J) :=
    (Commute.refl J |>.smul_left (Complex.I * (s : ℂ))).exp_left
  refine htot.congr_deriv ?_
  unfold evolve
  simp only [Matrix.mul_smul, Matrix.smul_mul, neg_smul, smul_sub, sub_eq_add_neg,
    mul_neg, hcomm, mul_assoc, ← smul_neg, ← smul_add]

lemma norm_le_of_frozen_unitary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf_cont : Continuous f)
    (ψ : ℝ → ℝ → E) (R : ℝ → E) (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hψ_diag : ∀ x, ψ x x = f x)
    (hψ_norm : ∀ x z, ‖ψ x z‖ = ‖f x‖)
    (hderiv : ∀ x, HasDerivAt (fun z => f z - ψ x z) (R x) x)
    (hR_le : ∀ x, ‖R x‖ ≤ g x)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖f t‖ ≤ ‖f 0‖ + ∫ s in (0 : ℝ)..t, g s := by
  set B : ℝ → ℝ := fun x => ‖f 0‖ + ∫ s in (0 : ℝ)..x, g s
  have hB_deriv : ∀ x, HasDerivAt B (g x) x := by
    intro x
    exact (intervalIntegral.integral_hasDerivAt_right
      (hg_cont.intervalIntegrable 0 x)
      (hg_cont.stronglyMeasurableAtFilter MeasureTheory.volume (nhds x))
      hg_cont.continuousAt).const_add ‖f 0‖
  have hB_cont : ContinuousOn B (Set.Icc 0 t) :=
    fun x _ => (hB_deriv x).continuousAt.continuousWithinAt
  have hmain := image_le_of_liminf_slope_right_le_deriv_boundary
    (hf_cont.norm.continuousOn)
    (by simp [B])
    hB_cont
    (fun x _ => (hB_deriv x).hasDerivWithinAt)
    (fun x _ r hr => ?_)
  · exact hmain ⟨ht, le_rfl⟩
  · have hr' : ‖R x‖ < r := lt_of_le_of_lt (hR_le x) hr
    have hfreq := (hderiv x).hasDerivWithinAt.liminf_right_slope_norm_le hr'
    refine hfreq.mp (Filter.Eventually.mono self_mem_nhdsWithin (fun z hxz hz => ?_))
    rw [slope_def_field]
    have hpos : 0 < z - x := sub_pos.mpr hxz
    have hle : ‖f z‖ - ‖f x‖ ≤ ‖f z - ψ x z‖ - ‖f x - ψ x x‖ := by
      rw [hψ_diag x, sub_self, norm_zero, sub_zero, ← hψ_norm x z]
      exact norm_sub_norm_le (f z) (ψ x z)
    have hmul : (z - x)⁻¹ * (‖f z‖ - ‖f x‖) ≤ (z - x)⁻¹ * (‖f z - ψ x z‖ - ‖f x - ψ x x‖) :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (le_of_lt hpos))
    rw [div_eq_inv_mul]
    exact lt_of_le_of_lt hmul hz

lemma comm_H_eq_sum_meets (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hsupp : ∀ X, SupportedOn X (h X))
    (X : Finset Λ) (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hA : SupportedOn X A) :
    H h * A - A * H h =
      ∑ Z ∈ Finset.univ.filter (fun Z => meets Z X), (h Z * A - A * h Z) := by
  unfold H
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Z _ => ?_)
  split_ifs with hm
  · rfl
  · have hd : Disjoint Z X := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.not_nonempty_iff_eq_empty.mp hm
    rw [comm_disjoint (h Z) A Z X (hsupp Z) hA hd, sub_self]

lemma evolve_comm_H_eq_sum_meets_raw (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hsupp : ∀ X, SupportedOn X (h X))
    (X : Finset Λ) (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hA : SupportedOn X A) (s : ℝ) :
    H h * evolve (H h) s A - evolve (H h) s A * H h =
      ∑ Z ∈ Finset.univ.filter (fun Z => meets Z X),
        evolve (H h) s (h Z * A - A * h Z) := by
  have lhs_eq : H h * evolve (H h) s A - evolve (H h) s A * H h =
      evolve (H h) s (H h * A - A * H h) := by
    rw [evolve_sub, evolve_mul, evolve_mul, evolve_self]
  rw [lhs_eq, comm_H_eq_sum_meets h hsupp X A hA, evolve_sum]

end Aux_LHS_CommLR_27

attribute [local instance] Classical.propDecidable

open LatticeHamSim.CommLR Aux_LHS_CommLR_27 in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (h14 : ∀ X Y, ‖h X * h Y - h Y * h X‖ ≤
      2 * η * ‖h X‖ * ‖h Y‖)
    (Y : Finset Λ) (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hB : SupportedOn Y B) (X : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    DB h B X t ≤ DB h B X 0 +
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => meets Z X),
        2 * η * ∫ s in (0:ℝ)..t,
          ‖h Z‖ * ‖h X‖ * CB h B (Z ∪ X) s := by
  unfold DB
  set S : Finset (Finset Λ) := Finset.univ.filter (fun Z => meets Z X)
  set f : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => evolve (H h) s (h X) * B - B * evolve (H h) s (h X)
  set R : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => Complex.I • ∑ Z ∈ S,
      (evolve (H h) s (h Z * h X - h X * h Z) * B -
        B * evolve (H h) s (h Z * h X - h X * h Z))
  set ψ : ℝ → ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ := fun x _ => f x
  set g : ℝ → ℝ := fun s => ∑ Z ∈ S, 2 * η * (‖h Z‖ * ‖h X‖ * CB h B (Z ∪ X) s)
  have hf_cont : Continuous f := by
    unfold f
    have hev := continuous_evolve (H h) (h X)
    exact (hev.mul continuous_const).sub (continuous_const.mul hev)
  have hg_cont : Continuous g := by
    unfold g
    exact continuous_finset_sum S (fun Z _ =>
      continuous_const.mul (continuous_const.mul (continuous_CB h hherm B (Z ∪ X))))
  have hderiv : ∀ x, HasDerivAt (fun z => f z - ψ x z) (R x) x := by
    intro x
    have hdf : HasDerivAt f
        (Complex.I • ((H h * evolve (H h) x (h X) - evolve (H h) x (h X) * H h) * B -
          B * (H h * evolve (H h) x (h X) - evolve (H h) x (h X) * H h))) x := by
      have hev := hasDerivAt_evolve (H h) (h X) x
      have h1 := (hev.mul_const B).sub (hev.const_mul B)
      refine h1.congr_deriv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    have hdψ : HasDerivAt (fun z => ψ x z) 0 x := hasDerivAt_const x (f x)
    refine (hdf.sub hdψ).congr_deriv ?_
    rw [sub_zero]
    unfold R
    congr 1
    rw [evolve_comm_H_eq_sum_meets_raw h hsupp X (h X) (hsupp X) x]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hR_le : ∀ x, ‖R x‖ ≤ g x := by
    intro x
    unfold R g
    rw [norm_smul, Complex.norm_I, one_mul]
    refine (norm_sum_le S _).trans (Finset.sum_le_sum (fun Z _ => ?_))
    have hZ_sub : SupportedOn (Z ∪ X) (h Z) :=
      supportedOn_mono Finset.subset_union_left (hsupp Z)
    have hX_sub : SupportedOn (Z ∪ X) (h X) :=
      supportedOn_mono Finset.subset_union_right (hsupp X)
    have hcomm_supp : SupportedOn (Z ∪ X) (h Z * h X - h X * h Z) :=
      supportedOn_sub (supportedOn_mul hZ_sub hX_sub) (supportedOn_mul hX_sub hZ_sub)
    have hle1 := norm_comm_evolve_le_CB h hherm B (Z ∪ X) x (h Z * h X - h X * h Z) hcomm_supp
    have hle2 := h14 Z X
    have hcb_nn := cb_nonneg h hherm B (Z ∪ X) x
    calc ‖evolve (H h) x (h Z * h X - h X * h Z) * B -
          B * evolve (H h) x (h Z * h X - h X * h Z)‖
        ≤ ‖h Z * h X - h X * h Z‖ * CB h B (Z ∪ X) x := hle1
      _ ≤ (2 * η * ‖h Z‖ * ‖h X‖) * CB h B (Z ∪ X) x :=
          mul_le_mul_of_nonneg_right hle2 hcb_nn
      _ = 2 * η * (‖h Z‖ * ‖h X‖ * CB h B (Z ∪ X) x) := by ring
  have hmain := norm_le_of_frozen_unitary f hf_cont ψ R g hg_cont
    (fun _ => rfl) (fun _ _ => rfl) hderiv hR_le t ht
  have hint_eq : ∫ s in (0 : ℝ)..t, g s =
      ∑ Z ∈ S, 2 * η * ∫ s in (0 : ℝ)..t, ‖h Z‖ * ‖h X‖ * CB h B (Z ∪ X) s := by
    unfold g
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl (fun Z _ => ?_)
      exact intervalIntegral.integral_const_mul (2 * η) _
    · intro Z _
      exact (continuous_const.mul (continuous_const.mul (continuous_CB h hherm B (Z ∪ X)))).intervalIntegrable 0 t
  rwa [hint_eq] at hmain
