-- Prove2me | solution 1 for MasulloGRH.compact_approxNumber_minmax
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:14:30.873969+00:00
-- url     : https://prove2.me/submissions/0cdf3850-f01f-4219-8da9-7d9f1b6c096c

import Mathlib
import Definitions.Def_MasulloGRH_ApproximationNumbers
import Theorems.Thm_MasulloGRH_approxNumber_eq_inf_orthogonalComplement

set_option linter.unusedSectionVars false

open Set Module End
open scoped InnerProductSpace

namespace MasulloGRH

section MaximalDirection

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private lemma normalize_complex {x : E} (hx : x ≠ 0) :
    ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- A compact operator has a unit top singular direction whenever the
Hilbert domain is nonzero. The real eigenvalue of the normal operator
is the square of the operator norm. -/
private lemma compact_top_direction [Nontrivial E] (A : E →L[ℂ] F)
    (hA : IsCompactOperator A) :
    ∃ v : E, ‖v‖ = 1 ∧ (A.adjoint.comp A) v = (‖A‖ ^ 2 : ℝ) • v ∧ ‖A v‖ = ‖A‖ := by
  let C := A.adjoint.comp A
  by_cases h : A = 0
  · obtain ⟨u, hu⟩ := exists_ne (0 : E)
    refine ⟨((‖u‖⁻¹ : ℝ) : ℂ) • u, normalize_complex hu, ?_, ?_⟩ <;> simp [h]
  · have hD : IsCompactOperator C := hA.clm_comp A.adjoint
    have hPos : 0 ≤ C :=
      (ContinuousLinearMap.nonneg_iff_isPositive C).mpr (ContinuousLinearMap.isPositive_adjoint_comp_self A)
    have hCnorm : ‖C‖ = ‖A‖ ^ 2 := by simpa only [sq] using A.norm_adjoint_comp_self
    have hSpec := CStarAlgebra.norm_mem_spectrum_of_nonneg hPos
    have hComplex : (‖C‖ : ℂ) ∈ spectrum ℂ C := by
      exact_mod_cast spectrum.algebraMap_mem ℂ hSpec
    have hCpos : (0 : ℝ) < ‖C‖ := by rw [hCnorm]; exact sq_pos_of_pos (norm_pos_iff.mpr h)
    have hEig : HasEigenvalue (C : E →ₗ[ℂ] E) (‖C‖ : ℂ) :=
      (hD.hasEigenvalue_iff_mem_spectrum (by exact_mod_cast hCpos.ne')).mpr hComplex
    obtain ⟨u, hu, hune⟩ := hEig.exists_hasEigenvector
    have heu : C u = (‖C‖ : ℂ) • u := by
      exact mem_genEigenspace_one.mp hu
    let v : E := ((‖u‖⁻¹ : ℝ) : ℂ) • u
    have hv : ‖v‖ = 1 := normalize_complex hune
    have hCv : C v = (‖C‖ : ℂ) • v := by
      dsimp only [v]
      rw [map_smul, heu, smul_comm (((‖u‖⁻¹ : ℝ) : ℂ)) (‖C‖ : ℂ)]
    have hAv : ‖A v‖ = ‖A‖ := by
      rw [A.apply_norm_eq_sqrt_inner_adjoint_right]
      change Real.sqrt (RCLike.re ⟪v, C v⟫_ℂ) = ‖A‖
      have hInner : RCLike.re ⟪v, C v⟫_ℂ = ‖C‖ := by
        rw [hCv, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
        simp
      rw [hInner, hCnorm, Real.sqrt_sq (norm_nonneg A)]
    refine ⟨v, hv, ?_, hAv⟩
    change C v = _
    rw [hCv, hCnorm]
    exact Complex.coe_smul _ _

private lemma exists_unit_in_submodule_ker_of_rank_lt (R : E →L[ℂ] F)
    (V : Submodule ℂ E) [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ (LinearMap.range (R : E →ₗ[ℂ] F))]
    (hRank : finrank ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) < finrank ℂ V) :
    ∃ x : E, x ∈ V ∧ ‖x‖ = 1 ∧ R x = 0 := by
  let T : V →ₗ[ℂ] F := (R : E →ₗ[ℂ] F).domRestrict V
  have hle : T.range ≤ LinearMap.range (R : E →ₗ[ℂ] F) := by
    rintro y ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hLT := (Submodule.finrank_mono hle).trans_lt hRank
  have hdim := T.finrank_range_add_finrank_ker
  have hpos : 0 < finrank ℂ T.ker := by omega
  let _ : Nontrivial T.ker := (Module.finrank_pos_iff_of_free ℂ T.ker).mp hpos
  obtain ⟨u, hu⟩ := exists_ne (0 : T.ker)
  let x : E := (u : V)
  have hx : x ≠ 0 := by
    intro he
    apply hu
    apply Subtype.ext
    apply Subtype.ext
    exact he
  have hRx : R x = 0 := u.property
  refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, V.smul_mem _ (u : V).property, normalize_complex hx, ?_⟩
  rw [map_smul, hRx, smul_zero]

private lemma exists_unit_in_submodule_orthogonal (K V : Submodule ℂ E)
    [FiniteDimensional ℂ K] [FiniteDimensional ℂ V] (h : finrank ℂ K < finrank ℂ V) :
    ∃ x : E, x ∈ V ∧ ‖x‖ = 1 ∧ x ∈ Kᗮ := by
  let T := K.orthogonalProjectionOnto
  have hr : finrank ℂ (LinearMap.range (T : E →ₗ[ℂ] K)) < finrank ℂ V :=
    (Submodule.finrank_le _).trans_lt h
  obtain ⟨v, hv, hvn, hz⟩ := exists_unit_in_submodule_ker_of_rank_lt T V hr
  refine ⟨v, hv, hvn, ?_⟩
  rw [← K.ker_orthogonalProjectionOnto]
  exact hz

private lemma exists_submodule_of_dim {m : ℕ} (hm : (m : Cardinal) ≤ Module.rank ℂ E) :
    ∃ V : Submodule ℂ E, FiniteDimensional ℂ V ∧ finrank ℂ V = m := by
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hm
  exact ⟨Submodule.span ℂ (range v), FiniteDimensional.span_of_finite ℂ (finite_range v),
    by simp [finrank_span_eq_card hv]⟩

private lemma restriction_norm_antitone (A : E →L[ℂ] F) {K V : Submodule ℂ E} (h : K ≤ V) :
    ‖A.comp Vᗮ.subtypeL‖ ≤ ‖A.comp Kᗮ.subtypeL‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (A.comp Vᗮ.subtypeL)
    (norm_nonneg (A.comp Kᗮ.subtypeL))
  intro x
  let y : Kᗮ := ⟨x, Submodule.orthogonal_le h x.property⟩
  exact (A.comp Kᗮ.subtypeL).le_opNorm y

private lemma extend_by_top_direction (A : E →L[ℂ] F) (hA : IsCompactOperator A)
    (K : Submodule ℂ E) [FiniteDimensional ℂ K]
    (hroom : ((finrank ℂ K + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ E)
    (hInv : ∀ x ∈ K, (A.adjoint.comp A) x ∈ K)
    (hLower : ∀ x ∈ K, ‖A.comp Kᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖) :
    ∃ V : Submodule ℂ E, FiniteDimensional ℂ V ∧ K ≤ V ∧
      finrank ℂ V = finrank ℂ K + 1 ∧
      (∀ x ∈ V, (A.adjoint.comp A) x ∈ V) ∧
      (∀ x ∈ V, ‖A.comp Kᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖) := by
  obtain ⟨W, hW, hdimW⟩ := exists_submodule_of_dim (E := E) hroom
  let _ : FiniteDimensional ℂ W := hW
  obtain ⟨z, _, hz, hzK⟩ := exists_unit_in_submodule_orthogonal K W
    (by rw [hdimW]; omega)
  let w : Kᗮ := ⟨z, hzK⟩
  have hw : w ≠ 0 := by
    intro he
    have he' := congrArg (fun x : Kᗮ ↦ ‖x‖) he
    change ‖z‖ = ‖(0 : E)‖ at he'
    rw [hz, norm_zero] at he'
    norm_num at he'
  let _ : Nontrivial Kᗮ := nontrivial_of_ne w 0 hw
  let B := A.comp Kᗮ.subtypeL
  let C := A.adjoint.comp A
  have hC : C.IsSymmetric := (ContinuousLinearMap.isPositive_adjoint_comp_self A).isSymmetric
  have hB : IsCompactOperator B := hA.comp_clm Kᗮ.subtypeL
  obtain ⟨v, hv, hEig, hAv⟩ := compact_top_direction B hB
  let u : E := v
  have hu : ‖u‖ = 1 := hv
  have hun : u ≠ 0 := by
    intro he
    rw [he, norm_zero] at hu
    norm_num at hu
  have huK : u ∈ Kᗮ := v.property
  have hnot : u ∉ K := by
    intro hm
    have hI := (K.mem_orthogonal u).mp huK u hm
    exact hun (inner_self_eq_zero.mp hI)
  have hCvorth : C u ∈ Kᗮ := by
    apply (K.mem_orthogonal (C u)).mpr
    intro x hx
    change ⟪x, (C : E →ₗ[ℂ] E) u⟫_ℂ = 0
    rw [← hC x u]
    exact (K.mem_orthogonal u).mp huK (C x) (hInv x hx)
  have hEigen : C u = (‖B‖ ^ 2 : ℝ) • u := by
    change ((A.comp Kᗮ.subtypeL).adjoint.comp (A.comp Kᗮ.subtypeL)) v = _ at hEig
    rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL] at hEig
    change Kᗮ.orthogonalProjectionOnto (C u) = _ at hEig
    have heq : Kᗮ.orthogonalProjectionOnto (C u) = (⟨C u, hCvorth⟩ : Kᗮ) :=
      Kᗮ.orthogonalProjectionOnto_mem_subspace_eq_self ⟨C u, hCvorth⟩
    rw [heq] at hEig
    exact congrArg (fun x : Kᗮ ↦ (x : E)) hEig
  let U := Submodule.span ℂ {u}
  let V := K ⊔ U
  let _ : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (finite_singleton u)
  have hfin : FiniteDimensional ℂ V := inferInstance
  have hKUV : K ≤ V := le_sup_left
  have hUV : U ≤ V := le_sup_right
  have hDis : Disjoint K U := Submodule.disjoint_span_singleton_of_notMem hnot
  have hdim : finrank ℂ V = finrank ℂ K + 1 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq K U
    rw [hDis.eq_bot, finrank_bot, add_zero] at hd
    rw [show finrank ℂ U = 1 from finrank_span_singleton hun] at hd
    exact hd
  refine ⟨V, hfin, hKUV, hdim, ?_, ?_⟩
  · intro x hx
    obtain ⟨x₀, hx₀, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change C (x₀ + a • u) ∈ V
    rw [map_add, map_smul, hEigen]
    exact V.add_mem (hKUV (hInv x₀ hx₀)) (V.smul_mem _ (V.smul_mem _ (hUV (Submodule.subset_span (by simp)))))
  · intro x hx
    obtain ⟨x₀, hx₀, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change ‖B‖ * ‖x₀ + a • u‖ ≤ ‖A (x₀ + a • u)‖
    have hInn : ⟪x₀, u⟫_ℂ = 0 := (K.mem_orthogonal u).mp huK x₀ hx₀
    have hInnA : ⟪A x₀, A u⟫_ℂ = 0 := by
      rw [← A.adjoint_inner_left]
      exact (K.mem_orthogonal u).mp huK (C x₀) (hInv x₀ hx₀)
    have hInn₁ : ⟪x₀, a • u⟫_ℂ = 0 := by rw [inner_smul_right, hInn, mul_zero]
    have hInn₂ : ⟪A x₀, a • A u⟫_ℂ = 0 := by rw [inner_smul_right, hInnA, mul_zero]
    have hEq₁ : ‖x₀ + a • u‖ ^ 2 = ‖x₀‖ ^ 2 + ‖a • u‖ ^ 2 := by
      simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x₀ (a • u) hInn₁
    have hEq₂ : ‖A x₀ + a • A u‖ ^ 2 = ‖A x₀‖ ^ 2 + ‖a • A u‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (A x₀) (a • A u) hInn₂
    have huA : ‖A u‖ = ‖B‖ := hAv
    have hBase : ‖B‖ * ‖x₀‖ ≤ ‖A x₀‖ := hLower x₀ hx₀
    have hBaseSq : (‖B‖ * ‖x₀‖) ^ 2 ≤ ‖A x₀‖ ^ 2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hBase
    rw [map_add, map_smul]
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [mul_pow, hEq₁, hEq₂]
    simp only [norm_smul, hu, huA, mul_one]
    nlinarith only [hBaseSq]

private lemma exists_invariant_lower_plane (A : E →L[ℂ] F) (hA : IsCompactOperator A)
    (m : ℕ) (hm : (m : Cardinal) ≤ Module.rank ℂ E) :
    ∃ K : Submodule ℂ E, FiniteDimensional ℂ K ∧ finrank ℂ K = m ∧
      (∀ x ∈ K, (A.adjoint.comp A) x ∈ K) ∧
      (∀ x ∈ K, ‖A.comp Kᗮ.subtypeL‖ * ‖x‖ ≤ ‖A x‖) := by
  induction m with
  | zero =>
    refine ⟨⊥, inferInstance, by simp only [finrank_bot], ?_, ?_⟩
    · intro x hx
      have hx' : x = 0 := by simpa using hx
      simp [hx']
    · intro x hx
      have hx' : x = 0 := by simpa using hx
      simp [hx']
  | succ m ih =>
    have hprev : (m : Cardinal) ≤ Module.rank ℂ E :=
      le_trans (by exact_mod_cast Nat.le_succ m) hm
    obtain ⟨K, hKfinite, hK, hInv, hLower⟩ := ih hprev
    let _ : FiniteDimensional ℂ K := hKfinite
    have hcap : ((finrank ℂ K + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ E := by
      simpa only [hK, Nat.succ_eq_add_one] using hm
    obtain ⟨V, hVfinite, hKV, hV, hInvV, hLowerV⟩ := extend_by_top_direction A hA K hcap hInv hLower
    refine ⟨V, hVfinite, hV.trans (by rw [hK]), hInvV, ?_⟩
    intro x hx
    exact (mul_le_mul_of_nonneg_right (restriction_norm_antitone A hKV) (norm_nonneg x)).trans
      (hLowerV x hx)

private lemma approxNumber_le_restriction (A : E →L[ℂ] F)
    (K : Submodule ℂ E) [FiniteDimensional ℂ K] {m : ℕ} (hm : 0 < m) (hK : finrank ℂ K < m) :
    approxNumber m A ≤ ‖A.comp Kᗮ.subtypeL‖ := by
  rw [approxNumber_eq_inf_orthogonalComplement hm]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨L, _, _, rfl⟩
    exact norm_nonneg (A.comp Lᗮ.subtypeL)
  · exact ⟨K, inferInstance, hK, rfl⟩

private lemma lower_plane_bound_le_approxNumber (A : E →L[ℂ] F)
    (V : Submodule ℂ E) [FiniteDimensional ℂ V] {m : ℕ} (hm : 0 < m)
    (hV : m ≤ finrank ℂ V) {c : ℝ} (hLower : ∀ x ∈ V, c * ‖x‖ ≤ ‖A x‖) :
    c ≤ approxNumber m A := by
  unfold approxNumber
  apply le_csInf
  · refine ⟨‖A - 0‖, 0, ?_, rfl⟩
    change FiniteDimensional ℂ (LinearMap.range (0 : E →ₗ[ℂ] F)) ∧
      finrank ℂ (LinearMap.range (0 : E →ₗ[ℂ] F)) < m
    rw [LinearMap.range_zero, finrank_bot]
    exact ⟨inferInstance, hm⟩
  · rintro r ⟨R, hR, rfl⟩
    let _ : FiniteDimensional ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) := hR.1
    obtain ⟨x, hx, hnorm, hRx⟩ :=
      exists_unit_in_submodule_ker_of_rank_lt R V (hR.2.trans_le hV)
    have hh := hLower x hx
    have hNorm := (A - R).le_opNorm x
    have hh' : c ≤ ‖A x‖ := by simpa only [hnorm, mul_one] using hh
    have hNorm' : ‖A x‖ ≤ ‖A - R‖ := by simpa only [hnorm, mul_one, sub_apply, hRx, sub_zero] using hNorm
    exact hh'.trans hNorm'

/-- Compact attainment of both variational expressions in (C.3.5.4),
with `m + 1` the one-based approximation-number index. The plane `K`
attains the restriction-norm infimum and `V` attains the largest lower
bound on the unit sphere among all planes of dimension `m + 1`. -/
theorem compact_approxNumber_minmax (A : E →L[ℂ] F) (hA : IsCompactOperator A)
    (m : ℕ) (hm : ((m + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ E) :
    ∃ K V : Submodule ℂ E, FiniteDimensional ℂ K ∧ FiniteDimensional ℂ V ∧
      finrank ℂ K = m ∧ finrank ℂ V = m + 1 ∧ K ≤ V ∧
      ‖A.comp Kᗮ.subtypeL‖ = approxNumber (m + 1) A ∧
      (∀ x ∈ V, approxNumber (m + 1) A * ‖x‖ ≤ ‖A x‖) ∧
      ∀ W : Submodule ℂ E, FiniteDimensional ℂ W → finrank ℂ W = m + 1 →
        ∃ x : E, x ∈ W ∧ ‖x‖ = 1 ∧ ‖A x‖ ≤ approxNumber (m + 1) A := by
  have hRoom : (m : Cardinal) ≤ Module.rank ℂ E :=
    le_trans (by exact_mod_cast Nat.le_succ m) hm
  obtain ⟨K, hKfinite, hK, hInv, hLower⟩ := exists_invariant_lower_plane A hA m hRoom
  let _ : FiniteDimensional ℂ K := hKfinite
  have hcap : ((finrank ℂ K + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ E := by
    rwa [hK]
  obtain ⟨V, hVfinite, hKV, hV, _, hLowerV⟩ := extend_by_top_direction A hA K hcap hInv hLower
  let _ : FiniteDimensional ℂ V := hVfinite
  rw [hK] at hV
  have heq : ‖A.comp Kᗮ.subtypeL‖ = approxNumber (m + 1) A := by
    apply le_antisymm
    · exact lower_plane_bound_le_approxNumber A V (by omega) hV.ge hLowerV
    · exact approxNumber_le_restriction A K (by omega) (by omega)
  refine ⟨K, V, hKfinite, hVfinite, hK, hV, hKV, heq, ?_, ?_⟩
  · rwa [← heq]
  · intro W hW hdim
    let _ : FiniteDimensional ℂ W := hW
    obtain ⟨x, hxW, hnorm, hxK⟩ := exists_unit_in_submodule_orthogonal K W (by omega)
    refine ⟨x, hxW, hnorm, ?_⟩
    have hNorm := (A.comp Kᗮ.subtypeL).le_opNorm (⟨x, hxK⟩ : Kᗮ)
    change ‖A x‖ ≤ ‖A.comp Kᗮ.subtypeL‖ * ‖x‖ at hNorm
    simpa only [heq, hnorm, mul_one] using hNorm

end MaximalDirection

end MasulloGRH

open MasulloGRH

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (A : E →L[ℂ] F) (hA : IsCompactOperator A)
    (m : ℕ) (hm : ((m + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ E) :
    ∃ K V : Submodule ℂ E, FiniteDimensional ℂ K ∧ FiniteDimensional ℂ V ∧
      finrank ℂ K = m ∧ finrank ℂ V = m + 1 ∧ K ≤ V ∧
      ‖A.comp Kᗮ.subtypeL‖ = approxNumber (m + 1) A ∧
      (∀ x ∈ V, approxNumber (m + 1) A * ‖x‖ ≤ ‖A x‖) ∧
      ∀ W : Submodule ℂ E, FiniteDimensional ℂ W → finrank ℂ W = m + 1 →
        ∃ x : E, x ∈ W ∧ ‖x‖ = 1 ∧ ‖A x‖ ≤ approxNumber (m + 1) A :=
  compact_approxNumber_minmax A hA m hm
