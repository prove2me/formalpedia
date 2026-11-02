-- Prove2me | solution 1 for LatticeHamSim.StrictLR.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:05:46.212682+00:00
-- url     : https://prove2.me/submissions/5f1146c1-6a3b-4d1b-956b-acef3f5b054d

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Aux_LHS_24

open LatticeHamSim.CommLR LatticeHamSim.StrictLR

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

lemma evolve_isHermitian (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hJ : J.IsHermitian)
    (s : ℝ) (M : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hM : M.IsHermitian) :
    (evolve J s M).IsHermitian := by
  change star (evolve J s M) = evolve J s M
  have hsa : star J = J := hJ
  have hUV := exp_mul_exp_neg J s
  have hstarU : star (NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) *
      NormedSpace.exp ((Complex.I * (s : ℂ)) • J) = 1 := by
    have hs : ((s : ℂ) • J) ∈ selfAdjoint (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
    have hU := (Unitary.mem_iff.mp (selfAdjoint.expUnitary ⟨(s : ℂ) • J, hs⟩).prop).1
    simpa only [selfAdjoint.expUnitary_coe, smul_smul] using hU
  have hU_star : star (NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) =
      NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) := by
    calc star (NormedSpace.exp ((Complex.I * (s : ℂ)) • J))
        = star (NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) *
          (NormedSpace.exp ((Complex.I * (s : ℂ)) • J) *
            NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) := by rw [hUV, mul_one]
      _ = (star (NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) *
            NormedSpace.exp ((Complex.I * (s : ℂ)) • J)) *
            NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) := by rw [mul_assoc]
      _ = NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) := by rw [hstarU, one_mul]
  have hV_star : star (NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J)) =
      NormedSpace.exp ((Complex.I * (s : ℂ)) • J) := by
    rw [← hU_star, star_star]
  have hMs : star M = M := hM
  unfold evolve
  rw [star_mul, star_mul, hV_star, hU_star, hMs, mul_assoc]

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

lemma continuous_DB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) :
    Continuous (fun s : ℝ => DB h B Z s) := by
  unfold DB
  have hev := continuous_evolve (H h) (h Z)
  exact ((hev.mul continuous_const).sub (continuous_const.mul hev)).norm

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

lemma hasDerivAt_evolve_sub (J M : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => evolve J (u - s) M)
      (Complex.I • (J * M - M * J)) s := by
  have h1 : HasDerivAt (fun u : ℝ => evolve J u M)
      (Complex.I • (J * M - M * J)) (s - s) := by
    rw [sub_self]
    simpa [evolve_zero] using hasDerivAt_evolve J M 0
  have h2 : HasDerivAt (fun u : ℝ => u - s) 1 s := by
    simpa using (hasDerivAt_id s).sub_const s
  simpa [Function.comp_def, one_smul] using HasDerivAt.scomp (h := fun u : ℝ => u - s) s h1 h2

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

lemma evolve_comm_H_eq_sum_meets (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hsupp : ∀ X, SupportedOn X (h X))
    (X : Finset Λ) (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hA : SupportedOn X A) (s : ℝ) :
    H h * evolve (H h) s A - evolve (H h) s A * H h =
      ∑ Z ∈ Finset.univ.filter (fun Z => meets Z X),
        (evolve (H h) s (h Z) * evolve (H h) s A - evolve (H h) s A * evolve (H h) s (h Z)) := by
  have lhs_eq : H h * evolve (H h) s A - evolve (H h) s A * H h =
      evolve (H h) s (H h * A - A * H h) := by
    rw [evolve_sub, evolve_mul, evolve_mul, evolve_self]
  rw [lhs_eq, comm_H_eq_sum_meets h hsupp X A hA, evolve_sum]
  refine Finset.sum_congr rfl (fun Z _ => ?_)
  rw [evolve_sub, evolve_mul, evolve_mul]

end Aux_LHS_24

open LatticeHamSim.CommLR LatticeHamSim.StrictLR Aux_LHS_24 in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    LatticeHamSim.CommLR.CB h B X t ≤ LatticeHamSim.CommLR.CB h B X 0 +
      ∑ Z ∈ Finset.univ.filter (fun Z => LatticeHamSim.CommLR.meets Z X), 2 * ∫ s in (0 : ℝ)..t, LatticeHamSim.CommLR.DB h B Z s := by
  unfold CB
  refine csSup_le (cb_set_nonempty h B X t) ?_
  rintro r ⟨A, hA, hA1, rfl⟩
  set S : Finset (Finset Λ) := Finset.univ.filter (fun Z => meets Z X)
  set f : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => evolve (H h) s A * B - B * evolve (H h) s A
  set G : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => ∑ Z ∈ S, evolve (H h) s (h Z)
  set R : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => Complex.I • ∑ Z ∈ S,
      ((evolve (H h) s (h Z) * B - B * evolve (H h) s (h Z)) * evolve (H h) s A -
        evolve (H h) s A * (evolve (H h) s (h Z) * B - B * evolve (H h) s (h Z)))
  set ψ : ℝ → ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun x z => evolve (G x) (z - x) (f x)
  set g : ℝ → ℝ := fun s => ∑ Z ∈ S, 2 * DB h B Z s
  have hf_cont : Continuous f := by
    unfold f
    have hev := continuous_evolve (H h) A
    exact (hev.mul continuous_const).sub (continuous_const.mul hev)
  have hg_cont : Continuous g := by
    unfold g
    exact continuous_finset_sum S (fun Z _ => continuous_const.mul (continuous_DB h B Z))
  have hψ_diag : ∀ x, ψ x x = f x := by
    intro x
    unfold ψ
    rw [sub_self, evolve_zero]
  have hG_herm : ∀ x, (G x).IsHermitian := by
    intro x
    change star (G x) = G x
    unfold G
    rw [star_sum]
    exact Finset.sum_congr rfl (fun Z _ => evolve_isHermitian (H h) (H_isHermitian h hherm) x (h Z) (hherm Z))
  have hψ_norm : ∀ x z, ‖ψ x z‖ = ‖f x‖ := by
    intro x z
    exact evolve_norm_of_isHermitian (G x) (hG_herm x) (z - x) (f x)
  have hderiv : ∀ x, HasDerivAt (fun z => f z - ψ x z) (R x) x := by
    intro x
    have hdf : HasDerivAt f
        (Complex.I • ((H h * evolve (H h) x A - evolve (H h) x A * H h) * B -
          B * (H h * evolve (H h) x A - evolve (H h) x A * H h))) x := by
      have hev := hasDerivAt_evolve (H h) A x
      have h1 := (hev.mul_const B).sub (hev.const_mul B)
      refine h1.congr_deriv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    have hdψ : HasDerivAt (fun z => ψ x z) (Complex.I • (G x * f x - f x * G x)) x :=
      hasDerivAt_evolve_sub (G x) (f x) x
    refine (hdf.sub hdψ).congr_deriv ?_
    rw [← smul_sub]
    unfold R G f
    congr 1
    rw [evolve_comm_H_eq_sum_meets h hsupp X A hA x]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun Z _ => ?_)
    noncomm_ring
  have hR_le : ∀ x, ‖R x‖ ≤ g x := by
    intro x
    unfold R g
    rw [norm_smul, Complex.norm_I, one_mul]
    refine (norm_sum_le S _).trans (Finset.sum_le_sum (fun Z _ => ?_))
    have hc := comm_bound (evolve (H h) x (h Z) * B - B * evolve (H h) x (h Z)) (evolve (H h) x A)
    rw [evolve_norm h hherm x A] at hc
    change ‖(evolve (H h) x (h Z) * B - B * evolve (H h) x (h Z)) * evolve (H h) x A -
        evolve (H h) x A * (evolve (H h) x (h Z) * B - B * evolve (H h) x (h Z))‖ ≤
      2 * DB h B Z x
    unfold DB
    nlinarith [norm_nonneg (evolve (H h) x (h Z) * B - B * evolve (H h) x (h Z))]
  have hmain := norm_le_of_frozen_unitary f hf_cont ψ R g hg_cont hψ_diag hψ_norm hderiv hR_le t ht
  have hf0_le : ‖f 0‖ ≤ sSup {r : ℝ | ∃ M : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X M ∧ ‖M‖ ≤ 1 ∧
      r = ‖evolve (H h) 0 M * B - B * evolve (H h) 0 M‖} :=
    le_csSup (cb_bddAbove h hherm B X 0) ⟨A, hA, hA1, rfl⟩
  have hint_eq : ∫ s in (0 : ℝ)..t, g s = ∑ Z ∈ S, 2 * ∫ s in (0 : ℝ)..t, DB h B Z s := by
    unfold g
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl (fun Z _ => ?_)
      exact intervalIntegral.integral_const_mul 2 _
    · intro Z _
      exact (continuous_const.mul (continuous_DB h B Z)).intervalIntegrable 0 t
  rw [hint_eq] at hmain
  exact hmain.trans (add_le_add hf0_le le_rfl)
