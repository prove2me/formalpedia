-- Prove2me | solution 1 for MasulloGRH.trace_of_diagonal_frequency_bands
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:35:43.970423+00:00
-- url     : https://prove2.me/submissions/dc9dd4a9-6253-4c5c-8795-76695e8761e2

import Theorems.Thm_MasulloGRH_nuclear_of_summable_rank_mul_opNorm
import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series
open MasulloGRH
open scoped BigOperators
set_option autoImplicit false

private lemma padded_sum {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (d : ℕ) (g : ℕ → E) (hg : ∀ i, d ≤ i → g i = 0) :
    HasSum g (∑ i : Fin d, g i.val) := by
  rw [Fin.sum_univ_eq_sum_range]
  exact hasSum_sum_of_ne_finset_zero (fun i hi => hg i (Nat.le_of_not_gt (by simpa using hi)))

private lemma trace_on_finite_span {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype ι]
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] (B : Module.Basis ι ℂ W)
    (A : H →L[ℂ] H) (hA : ∀ u, A u ∈ W) :
    operatorTrace A = ∑ i, B.coord i (⟨A (B i : H), hA _⟩ : W) := by
  classical
  let d := Fintype.card ι
  let e : Fin d ≃ ι := (Fintype.equivFin ι).symm
  let L (i : ι) : H →L[ℂ] ℂ := (LinearMap.toContinuousLinearMap (B.coord i)).comp (A.codRestrict W hA)
  let x (j : ℕ) : H := if h : j < d then (InnerProductSpace.toDual ℂ H).symm (L (e ⟨j,h⟩)) else 0
  let y (j : ℕ) : H := if h : j < d then (B (e ⟨j,h⟩) : H) else 0
  have hpair (j : Fin d) (u : H) : inner ℂ (x j.val) u = L (e j) u := by
    simp [x, j.isLt, InnerProductSpace.toDual_symm_apply]
  have hy (j : Fin d) : y j.val = (B (e j) : H) := by simp [y, j.isLt]
  have hy0 {j : ℕ} (hj : d ≤ j) : y j = 0 := by simp [y, Nat.not_lt.mpr hj]
  have hcost := padded_sum d (fun j => ‖x j‖ * ‖y j‖) (fun j hj => by simp [hy0 hj])
  have hrepr (u : H) : HasSum (fun j => inner ℂ (x j) u • y j) (A u) := by
    have h := padded_sum d (fun j => inner ℂ (x j) u • y j) (fun j hj => by simp [hy0 hj])
    convert h using 1
    simp only [hpair, hy]
    rw [e.sum_comp (fun i => L i u • (B i : H))]
    have hb := congrArg W.subtype (B.sum_repr ((A.codRestrict W hA) u))
    rw [map_sum] at hb
    simpa only [L, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, map_smul, Submodule.subtype_apply, ContinuousLinearMap.coe_codRestrict_apply] using hb.symm
  rw [operatorTrace_of_nuclear_series A x y hcost.summable hrepr,
    (padded_sum d (fun j => inner ℂ (x j) (y j)) (fun j hj => by simp [hy0 hj])).tsum_eq]
  simp only [hpair, hy]
  exact e.sum_comp (fun i => L i (B i : H))

private lemma range_in_band {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ι → H) (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] (A : H →L[ℂ] H)
    (hAW : ∀ i, A (v i) ∈ W) (u : H) : A u ∈ W := by
  let P := W.comap A.toLinearMap
  have hle : Submodule.span ℂ (Set.range v) ≤ P := Submodule.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    exact hAW i)
  have hclosed : IsClosed (P : Set H) := W.closed_of_finiteDimensional.preimage A.continuous
  exact closure_minimal hle hclosed (hd u)

private lemma trace_diagonal_band {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v : ι → H) (hl : LinearIndependent ℂ v)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (F : Finset ι) (A : H →L[ℂ] H) (a : ι → ℂ)
    (ha : ∀ i, A (v i) = a i • v i) (hF : ∀ i, i ∉ F → a i = 0) :
    operatorTrace A = ∑ i ∈ F, a i := by
  classical
  let w (i : F) := v i.val
  let W := Submodule.span ℂ (Set.range w)
  let B : Module.Basis F ℂ W := Module.Basis.span (hl.comp Subtype.val Subtype.val_injective)
  have hB (i : F) : (B i : H) = v i.val := Module.Basis.coe_span_apply _ i
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range w)
  have hAW : ∀ u, A u ∈ W := range_in_band v hd W A (by
    intro i
    rw [ha]
    by_cases hi : i ∈ F
    · exact W.smul_mem _ (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩)
    · simp [hF i hi])
  rw [trace_on_finite_span W B A hAW, ← Finset.sum_coe_sort F a]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (⟨A (B i : H), hAW _⟩ : W) = a i.val • B i := by
    apply Subtype.ext
    simpa [hB] using ha i.val
  rw [heq, map_smul]
  simp [Module.Basis.coord_apply]

theorem solution {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : ι → H) (hl : LinearIndependent ℂ v)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (F : ℕ → Finset ι) (A : ℕ → H →L[ℂ] H) (a : ℕ → ι → ℂ)
    (hA : ∀ n i, A n (v i) = a n i • v i)
    (hsupp : ∀ n i, i ∉ F n → a n i = 0)
    (hc : Summable fun n => ((F n).card : ℝ) * ‖A n‖)
    (T : H →L[ℂ] H) (m : ι → ℂ)
    (hpart : ∀ i, HasSum (fun n => a n i) (m i))
    (hT : ∀ i, T (v i) = m i • v i) :
    IsNuclearOperator T ∧ HasSum m (operatorTrace T) := by
  classical
  let w (n : ℕ) (i : F n) := v i.val
  let W (n : ℕ) := Submodule.span ℂ (Set.range (w n))
  have inst (n : ℕ) : FiniteDimensional ℂ (W n) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hW (n : ℕ) (u : H) : A n u ∈ W n := by
    apply range_in_band v hd (W n) (A n) _ u
    intro i
    rw [hA]
    by_cases hi : i ∈ F n
    · exact (W n).smul_mem _ (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩)
    · simp [hsupp n i hi]
  have hdim (n : ℕ) : Module.finrank ℂ (W n) = (F n).card := by
    rw [show W n = Submodule.span ℂ (Set.range (v ∘ (Subtype.val : F n → ι))) from rfl,
        finrank_span_eq_card (hl.comp Subtype.val Subtype.val_injective), Fintype.card_coe]
  have hnorm : Summable (fun n => ‖A n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hc
    intro n
    by_cases hn : (F n).Nonempty
    · exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast hn.card_pos)
    · have he : F n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hzero : A n = 0 := ContinuousLinearMap.ext_on hd (by
        rintro _ ⟨i,rfl⟩
        simp [hA, hsupp n i (by simp [he])])
      simp [hzero]
  have hsum := hnorm.of_norm.hasSum
  have happ (u : H) := ((ContinuousLinearMap.apply ℂ H) u).hasSum hsum
  have hEq : (∑' n, A n) = T := ContinuousLinearMap.ext_on hd (by
    rintro _ ⟨i,rfl⟩
    have h1 : HasSum (fun n => A n (v i)) ((∑' n, A n) (v i)) := happ (v i)
    have h2 : HasSum (fun n => A n (v i)) (T (v i)) := by
      simpa only [hA, hT] using (hpart i).smul_const (v i)
    exact h1.unique h2)
  have hAT : ∀ u, HasSum (fun n => A n u) (T u) := by
    intro u
    rw [← hEq]
    exact happ u
  have ⟨hnuc,htrace⟩ := nuclear_of_summable_rank_mul_opNorm A W hW (by simpa only [hdim] using hc) T hAT
  refine ⟨hnuc, ?_⟩
  have ha (n : ℕ) (i : ι) : ‖a n i‖ ≤ ‖A n‖ := by
    have hv : 0 < ‖v i‖ := norm_pos_iff.mpr (hl.ne_zero i)
    apply (mul_le_mul_iff_left₀ hv).mp
    simpa only [← norm_smul, ← hA] using (A n).le_opNorm (v i)
  have hrow (n : ℕ) : HasSum (a n) (operatorTrace (A n)) := by
    rw [trace_diagonal_band v hl hd (F n) (A n) (a n) (hA n) (hsupp n)]
    exact hasSum_sum_of_ne_finset_zero (hsupp n)
  have hsumabs (n : ℕ) : HasSum (fun i => ‖a n i‖) (∑ i ∈ F n, ‖a n i‖) :=
    hasSum_sum_of_ne_finset_zero (fun i hi => by simp [hsupp n i hi])
  let f (p : ℕ × ι) := a p.1 p.2
  have habs : Summable (fun p => ‖f p‖) := by
    apply (summable_prod_of_nonneg (fun p => norm_nonneg (f p))).mpr
    refine ⟨fun n => (hsumabs n).summable, ?_⟩
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => norm_nonneg (a n i))) _ hc
    intro n
    rw [(hsumabs n).tsum_eq]
    exact (Finset.sum_le_sum (fun i (_ : i ∈ F n) => ha n i)).trans_eq (by simp)
  have hf := habs.of_norm.hasSum
  have htr : (∑' p, f p) = operatorTrace T := (hf.prod_fiberwise hrow).unique htrace
  rw [← htr]
  exact (Equiv.prodComm ℕ ι).symm.hasSum_iff.mpr hf |>.prod_fiberwise hpart
