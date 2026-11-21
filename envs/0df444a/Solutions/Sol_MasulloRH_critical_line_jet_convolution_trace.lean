-- Prove2me | solution 1 for MasulloRH.critical_line_jet_convolution_trace
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:59:02.115956+00:00
-- url     : https://prove2.me/submissions/56e59592-5a6c-4562-99ec-2043b2202c06

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear
import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_MasulloGRH_nuclear_of_summable_rank_mul_opNorm
import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series
import Theorems.Thm_MasulloRH_localized_fourier_multiplier
import Theorems.Thm_MasulloRH_weighted_zero_summability

section
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

theorem MasulloGRH.trace_of_triangular_frequency_bands {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ι → ℕ) (v : (Σ i, Fin (d i)) → H) (hl : LinearIndependent ℂ v)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (F : ℕ → Finset ι) (A : ℕ → H →L[ℂ] H) (a : ℕ → ι → ℂ)
    (c : ℕ → (i : ι) → Fin (d i) → Fin (d i) → ℂ)
    (hA : ∀ n i (r : Fin (d i)), A n (v ⟨i,r⟩) = a n i • v ⟨i,r⟩ +
        ∑ s ∈ Finset.Iio r, c n i r s • v ⟨i,s⟩)
    (hsupp : ∀ n i, i ∉ F n → ∀ r : Fin (d i), A n (v ⟨i,r⟩) = 0)
    (hc : Summable fun n => ((∑ i ∈ F n, d i : ℕ) : ℝ) * ‖A n‖)
    (T : H →L[ℂ] H) (m : ι → ℂ)
    (hpart : ∀ i, 0 < d i → HasSum (fun n => a n i) (m i))
    (hT : ∀ j, HasSum (fun n => A n (v j)) (T (v j))) :
    IsNuclearOperator T ∧ HasSum (fun i => (d i : ℂ) * m i) (operatorTrace T) := by
  classical
  let J := (i : ι) × Fin (d i)
  let E (n : ℕ) : Finset J := (F n).sigma fun _ => Finset.univ
  have hmem (n : ℕ) (j : J) : j ∈ E n ↔ j.1 ∈ F n := by
    rcases j with ⟨i,s⟩
    change (Sigma.mk i s) ∈ (F n).sigma (fun i => (Finset.univ : Finset (Fin (d i)))) ↔ i ∈ F n
    rw [Finset.mem_sigma]
    simp
  have hcard (n : ℕ) : (E n).card = ∑ i ∈ F n, d i := by
    exact (Finset.card_sigma (F n) (fun i => (Finset.univ : Finset (Fin (d i))))).trans (by simp)
  let W (n : ℕ) := Submodule.span ℂ (Set.range (v ∘ (Subtype.val : E n → J)))
  have inst (n : ℕ) : FiniteDimensional ℂ (W n) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hW (n : ℕ) (u : H) : A n u ∈ W n := by
    apply range_in_band v hd (W n) (A n) _ u
    rintro ⟨i,r⟩
    by_cases hi : i ∈ F n
    · have hb (s : Fin (d i)) : v ⟨i,s⟩ ∈ W n :=
        Submodule.subset_span ⟨⟨⟨i,s⟩,(hmem n _).mpr hi⟩,rfl⟩
      rw [hA]
      exact (W n).add_mem ((W n).smul_mem _ (hb r))
        ((W n).sum_mem (fun s _ => (W n).smul_mem _ (hb s)))
    · simpa only [hsupp n i hi r] using (W n).zero_mem
  have hdim (n : ℕ) : Module.finrank ℂ (W n) = (E n).card := by
    rw [show W n = Submodule.span ℂ (Set.range (v ∘ (Subtype.val : E n → J))) from rfl,
      finrank_span_eq_card (hl.comp Subtype.val Subtype.val_injective), Fintype.card_coe]
  have hcost : Summable (fun n => ((E n).card : ℝ) * ‖A n‖) := by simpa only [hcard] using hc
  have hnorm : Summable (fun n => ‖A n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hcost
    intro n
    by_cases hn : (E n).Nonempty
    · exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast hn.card_pos)
    · have hz : A n = 0 := ContinuousLinearMap.ext_on hd (by
        rintro _ ⟨⟨i,r⟩,rfl⟩
        exact hsupp n i (fun hi => hn ⟨⟨i,r⟩, (hmem n _).mpr hi⟩) r)
      simp [hz]
  have happ (u : H) := ((ContinuousLinearMap.apply ℂ H) u).hasSum hnorm.of_norm.hasSum
  have hEq : (∑' n, A n) = T := ContinuousLinearMap.ext_on hd (by
    rintro _ ⟨j,rfl⟩
    exact (happ (v j)).unique (hT j))
  have hAT (u : H) : HasSum (fun n => A n u) (T u) := by rw [← hEq]; exact happ u
  obtain ⟨hnuc, htrace⟩ := nuclear_of_summable_rank_mul_opNorm A W hW (by simpa only [hdim] using hcost) T hAT
  refine ⟨hnuc, ?_⟩
  have hlevel (n : ℕ) (i : ι) (hi : 0 < d i) :
      A n (v ⟨i,⟨0,hi⟩⟩) = a n i • v ⟨i,⟨0,hi⟩⟩ := by
    rw [hA]
    have h0 : Finset.Iio (⟨0,hi⟩ : Fin (d i)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      simp [Fin.lt_def]
    simp [h0]
  have ha (n : ℕ) (j : J) : ‖a n j.1‖ ≤ ‖A n‖ := by
    have hp := Nat.zero_lt_of_lt j.2.isLt
    let k : J := ⟨j.1,⟨0,hp⟩⟩
    apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr (hl.ne_zero k))).mp
    simpa only [← norm_smul, k, ← hlevel n j.1 hp] using (A n).le_opNorm (v k)
  have hzero (n : ℕ) (j : J) (hj : j ∉ E n) : a n j.1 = 0 := by
    have hp := Nat.zero_lt_of_lt j.2.isLt
    let k : J := ⟨j.1,⟨0,hp⟩⟩
    have h : a n j.1 • v k = 0 := (hlevel n j.1 hp).symm.trans (hsupp n j.1 (fun hi => hj ((hmem n j).mpr hi)) _)
    exact (smul_eq_zero.mp h).resolve_right (hl.ne_zero k)
  have hrow (n : ℕ) : HasSum (fun j : J => a n j.1) (operatorTrace (A n)) := by
    let B : Module.Basis (E n) ℂ (W n) := Module.Basis.span (hl.comp Subtype.val Subtype.val_injective)
    have hB (j : E n) : (B j : H) = v j.val := Module.Basis.coe_span_apply _ j
    have htr : operatorTrace (A n) = ∑ j ∈ E n, a n j.1 := by
      rw [trace_on_finite_span (W n) B (A n) (hW n), ← Finset.sum_coe_sort (E n) (fun j : J => a n j.1)]
      apply Finset.sum_congr rfl
      rintro ⟨⟨i,r⟩,hi⟩ _
      let e (s : Fin (d i)) : E n := ⟨⟨i,s⟩, (hmem n _).mpr ((hmem n ⟨i,r⟩).mp hi)⟩
      have heq : (⟨A n (B (e r) : H), hW n _⟩ : W n) =
          a n i • B (e r) + ∑ s ∈ Finset.Iio r, c n i r s • B (e s) := by
        apply Subtype.ext
        simpa only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, hB,e] using hA n i r
      change B.coord (e r) (⟨A n (B (e r) : H), hW n _⟩ : W n) = a n i
      rw [heq, map_add, map_smul, map_sum]
      have hoff (s : Fin (d i)) (hs : s ∈ Finset.Iio r) : B.coord (e r) (c n i r s • B (e s)) = 0 := by
        have hne : e s ≠ e r := by
          intro h
          have hs' : s = r := by
            exact (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2 |> eq_of_heq
          exact (Finset.mem_Iio.mp hs).ne hs'
        simp [Module.Basis.coord_apply,Ne.symm hne]
      rw [Finset.sum_eq_zero hoff]
      simp [Module.Basis.coord_apply]
    rw [htr]
    exact hasSum_sum_of_ne_finset_zero (hzero n)
  let f (p : ℕ × J) := a p.1 p.2.1
  have hsumabs (n : ℕ) : HasSum (fun j : J => ‖a n j.1‖) (∑ j ∈ E n, ‖a n j.1‖) :=
    hasSum_sum_of_ne_finset_zero (fun j hj => by simp [hzero n j hj])
  have habs : Summable (fun p => ‖f p‖) := by
    apply (summable_prod_of_nonneg (fun p => norm_nonneg (f p))).mpr
    refine ⟨fun n => (hsumabs n).summable, ?_⟩
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun j : J => norm_nonneg (a n j.1))) _ hcost
    intro n
    rw [(hsumabs n).tsum_eq]
    exact (Finset.sum_le_sum (fun j (_ : j ∈ E n) => ha n j)).trans_eq (by simp)
  have hf := habs.of_norm.hasSum
  have htr : (∑' p, f p) = operatorTrace T := (hf.prod_fiberwise hrow).unique htrace
  rw [← htr]
  have hall : HasSum (fun j : J => m j.1) (∑' p, f p) :=
    ((Equiv.prodComm ℕ J).symm.hasSum_iff.mpr hf).prod_fiberwise (fun j => hpart j.1 (Nat.zero_lt_of_lt j.2.isLt))
  exact hall.sigma (fun i => by simpa using (hasSum_fintype (fun _ : Fin (d i) => m i)))
end

section
open MeasureTheory Filter MasulloRH MasulloGRH
open scoped FourierTransform SchwartzMap BigOperators ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LocalizedFourier


private noncomputable def rawWindow (x : ℝ) : ℂ :=
  ((Real.smoothTransition (x+1) - Real.smoothTransition x : ℝ) : ℂ)

private lemma rawWindow_zero (x : ℝ) (hx : 1 ≤ |x|) : rawWindow x = 0 := by
  rcases le_abs.mp hx with h | h
  · simp [rawWindow, Real.smoothTransition.one_of_one_le h,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x+1)]
  · simp [rawWindow, Real.smoothTransition.zero_of_nonpos (by linarith : x ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : x+1 ≤ 0)]

private lemma rawWindow_smooth : ContDiff ℝ ∞ rawWindow := by
  have H : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (x+1) - Real.smoothTransition x) :=
    (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub Real.smoothTransition.contDiff
  exact Complex.ofRealCLM.contDiff.comp H

private lemma rawWindow_compact : HasCompactSupport rawWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(-1:ℝ)) (b:=1))
  intro x hx
  by_contra h
  apply hx
  apply rawWindow_zero
  by_contra! h'
  exact h ⟨(abs_lt.mp h').1.le, (abs_lt.mp h').2.le⟩

/-- A smooth integer-translate partition window, supported in the unit interval on each side of zero. -/
noncomputable def integerWindow : 𝓢(ℝ,ℂ) := rawWindow_compact.toSchwartzMap rawWindow_smooth

theorem integerWindow_zero (x : ℝ) (hx : 1 ≤ |x|) : integerWindow x = 0 := rawWindow_zero x hx

theorem integerWindow_range (x : ℝ) :
    (integerWindow x).im = 0 ∧ 0 ≤ (integerWindow x).re ∧ (integerWindow x).re ≤ 1 := by
  change (Complex.ofReal _).im = 0 ∧ 0 ≤ Real.smoothTransition (x+1) - Real.smoothTransition x ∧
    Real.smoothTransition (x+1) - Real.smoothTransition x ≤ 1
  exact ⟨rfl, sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith)),
    sub_le_self _ (Real.smoothTransition.nonneg x) |>.trans (Real.smoothTransition.le_one _)⟩

theorem integerWindow_local (x : ℝ) (j : ℤ) (h0 : j ≠ ⌊x⌋) (h1 : j ≠ ⌊x⌋+1) :
    integerWindow (x-(j:ℝ)) = 0 := by
  have hp := Int.floor_le x
  have hq := Int.lt_floor_add_one x
  apply integerWindow_zero
  by_cases hj : j < ⌊x⌋
  · have h : (j:ℝ) + 1 ≤ (⌊x⌋:ℝ) := by exact_mod_cast (show j+1 ≤ ⌊x⌋ by omega)
    exact le_abs.mpr (Or.inl (by linarith))
  · have h : (⌊x⌋:ℝ) + 2 ≤ (j:ℝ) := by exact_mod_cast (show ⌊x⌋+2 ≤ j by omega)
    exact le_abs.mpr (Or.inr (by linarith))

theorem integerWindow_hasSum (x : ℝ) : HasSum (fun j : ℤ => integerWindow (x-(j:ℝ))) 1 := by
  let p : ℤ := ⌊x⌋
  let f := fun j : ℤ => integerWindow (x-(j:ℝ))
  have hs : ∀ j ∉ ({p, p+1} : Finset ℤ), f j = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact integerWindow_local x j hj.1 hj.2
  have hp : (p:ℝ) ≤ x := Int.floor_le x
  have hq : x < (p:ℝ)+1 := Int.lt_floor_add_one x
  have hsum : ∑ j ∈ ({p,p+1} : Finset ℤ), f j = 1 := by
    rw [Finset.sum_pair (by omega : p ≠ p+1)]
    change ((Real.smoothTransition ((x-(p:ℝ))+1) - Real.smoothTransition (x-(p:ℝ)) : ℝ) : ℂ) +
      ((Real.smoothTransition ((x-((p+1:ℤ):ℝ))+1) - Real.smoothTransition (x-((p+1:ℤ):ℝ)) : ℝ) : ℂ) = 1
    simp only [Int.cast_add, Int.cast_one]
    rw [show x-((p:ℝ)+1)+1 = x-(p:ℝ) by ring,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x-(p:ℝ)+1),
      Real.smoothTransition.zero_of_nonpos (by linarith : x-((p:ℝ)+1) ≤ 0)]
    push_cast
    ring
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hs


end LocalizedFourier

namespace MasulloRH

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integratedOperator_exists
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (W : ℝ → ℝ) (A : ℝ)
    (hcont : ∀ u, Continuous (fun y => U y u))
    (hK : AEStronglyMeasurable K) (hKW : Integrable (fun y => ‖K y‖ * W y))
    (hW : ∀ y, 0 ≤ W y) (hA : 0 ≤ A) (hU : ∀ y, ‖U y‖ ≤ A * W y) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, K y • U y u) ∧
      ‖T‖ ≤ A * ∫ y : ℝ, ‖K y‖ * W y := by
  have hdom (u : H) (y : ℝ) :
      ‖K y • U y u‖ ≤ (‖K y‖ * W y) * (A * ‖u‖) := by
    rw [norm_smul]
    calc
      _ ≤ ‖K y‖ * ((A * W y) * ‖u‖) := by
        gcongr
        exact ((U y).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hU y) (norm_nonneg _))
      _ = _ := by ring
  have hi (u : H) : Integrable (fun y => K y • U y u) := by
    apply (hKW.mul_const (A * ‖u‖)).mono' (hK.smul (hcont u).aestronglyMeasurable)
    exact Eventually.of_forall (hdom u)
  let L : H →ₗ[ℂ] H := {
    toFun := fun u => ∫ y : ℝ, K y • U y u
    map_add' := by
      intro u v
      simp only [map_add, smul_add, integral_add (hi u) (hi v)]
    map_smul' := by
      intro c u
      simp only [map_smul, RingHom.id_apply]
      simp_rw [smul_comm (K _) c, integral_smul] }
  have hb (u : H) : ‖L u‖ ≤ (A * ∫ y : ℝ, ‖K y‖ * W y) * ‖u‖ := by
    calc
      _ ≤ ∫ y : ℝ, (‖K y‖ * W y) * (A * ‖u‖) := by
        exact norm_integral_le_of_norm_le (hKW.mul_const _) (Eventually.of_forall (hdom u))
      _ = _ := by rw [integral_mul_const]; ring
  have hC : 0 ≤ A * ∫ y : ℝ, ‖K y‖ * W y := mul_nonneg hA
    (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (hW y)))
  exact ⟨L.mkContinuous _ hb, fun _ => rfl, L.mkContinuous_norm_le hC hb⟩

theorem integratedOperator_eigen
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, K y • U y u)
    (character : ℝ → ℂ) (v : H) (hv : ∀ y, U y v = character y • v) :
    T v = (∫ y : ℝ, K y * character y) • v := by
  rw [hT]
  simp_rw [hv, smul_smul]
  exact integral_smul_const _ _

theorem integratedOperator_fourier
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, K y • U y u)
    (ξ : ℝ) (v : H)
    (hv : ∀ y : ℝ, U y v = Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • v) :
    T v = (𝓕 K ξ) • v := by
  rw [integratedOperator_eigen U K T hT _ v hv, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => mul_comm _ _

theorem integratedOperator_inverseFourier
    (U : ℝ → H →L[ℂ] H) (m : ℝ → ℂ) (T : H →L[ℂ] H)
    (hm : Integrable m) (hmF : Integrable (𝓕 m))
    (hT : ∀ u, T u = ∫ y : ℝ, (𝓕⁻ m) y • U y u)
    (ξ : ℝ) (hmξ : ContinuousAt m ξ) (v : H)
    (hv : ∀ y : ℝ, U y v = Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • v) :
    T v = m ξ • v := by
  rw [integratedOperator_fourier U (𝓕⁻ m) T hT ξ v hv, hm.fourier_fourierInv_eq hmF hmξ]


end MasulloRH

private lemma polynomial_band_count {ι : Type*} (ν : ι → ℝ)
    (hw : Summable fun i => 1/(1+(ν i)^2)) :
    ∃ F : ℤ → Finset ι, ∃ C : ℝ, 0 ≤ C ∧
      (∀ j i, i ∈ F j ↔ |ν i - j| ≤ 1) ∧
      ∀ j, ((F j).card : ℝ) ≤ C * (1 + |(j:ℝ)|)^2 := by
  classical
  let w (i : ι) : ℝ := 1 / (1 + (ν i)^2)
  let D (j : ℤ) := 2 * (1 + |(j:ℝ)|)^2
  have hD (j : ℤ) : 0 < D j := by dsimp [D]; positivity
  have hle {j : ℤ} {i : ι} (hi : |ν i - j| ≤ 1) : 1 / D j ≤ w i := by
    apply one_div_le_one_div_of_le (by positivity)
    have h : |ν i| ≤ 1 + |(j:ℝ)| := calc
      |ν i| = |ν i - j + j| := by ring_nf
      _ ≤ |ν i - j| + |(j:ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
    have hs := sq_le_sq₀ (abs_nonneg (ν i)) (by positivity : 0 ≤ 1+|(j:ℝ)|)
    dsimp [D]
    nlinarith [(sq_abs (ν i)), hs.mpr h, abs_nonneg (j:ℝ)]
  have hfinite (j : ℤ) : {i | |ν i - j| ≤ 1}.Finite := by
    have hev : ∀ᶠ i in cofinite, w i < 1 / D j :=
      hw.tendsto_cofinite_zero.eventually_lt_const (by positivity)
    apply (Filter.mem_cofinite.mp hev).subset
    intro i hi
    exact not_lt.mpr (hle hi)
  let F (j : ℤ) := (hfinite j).toFinset
  have hF (j : ℤ) (i : ι) : i ∈ F j ↔ |ν i - j| ≤ 1 := Set.Finite.mem_toFinset _
  refine ⟨F, 2 * ∑' i, w i, mul_nonneg (by norm_num) (tsum_nonneg (fun i => by dsimp [w]; positivity)), hF, ?_⟩
  intro j
  have hsum : ∑ i ∈ F j, 1 / D j ≤ ∑ i ∈ F j, w i :=
    Finset.sum_le_sum (fun i hi => hle ((hF j i).mp hi))
  have hupper := hsum.trans (hw.sum_le_tsum (F j) (fun _ _ => by positivity))
  have hdiv : ((F j).card : ℝ) / D j ≤ ∑' i, w i := by simpa [div_eq_mul_inv] using hupper
  have hcard := (div_le_iff₀ (hD j)).mp hdiv
  dsimp [D] at hcard
  linarith only [hcard]

private lemma summable_band_cost {ι E : Type*} [NormedAddCommGroup E]
    (A : ℤ → E) (F : ℤ → Finset ι) (C B : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ j, ((F j).card : ℝ) ≤ C * (1 + |(j:ℝ)|)^2)
    (hA : ∀ j : ℤ, (1 + |(j:ℝ)|)^4 * ‖A j‖ ≤ B) :
    Summable fun j => ((F j).card : ℝ) * ‖A j‖ := by
  have hnat : Summable (fun n : ℕ => 1/(1+|(n:ℝ)|)^2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    simpa [abs_of_nonneg, add_comm (1:ℝ) _, Real.rpow_two] using h
  have hint : Summable (fun j : ℤ => 1/(1+|(j:ℝ)|)^2) := by
    apply Summable.of_nat_of_neg <;> simpa using hnat
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hint.mul_left (C*B))
  intro j
  set x := 1 + |(j:ℝ)|
  have hx : 0 < x := by dsimp [x]; positivity
  calc
    _ ≤ (C * x^2) * ‖A j‖ := mul_le_mul_of_nonneg_right (hcount j) (norm_nonneg _)
    _ = (C * (x^4 * ‖A j‖)) / x^2 := by field_simp
    _ ≤ C * B / x^2 := by gcongr; exact hA j
    _ = _ := by ring

private lemma schwartz_weighted_integral (g : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun x : ℝ => (1+|x|)^k * ‖g x‖) := by
  have h := (g.integrable.norm.add (g.integrable_pow_mul volume k)).const_mul ((2:ℝ)^(k-1))
  apply h.mono' (by fun_prop)
  refine Eventually.of_forall fun x => ?_
  change ‖(1+|x|)^k * ‖g x‖‖ ≤ 2^(k-1) * (‖g x‖ + ‖x‖ ^ k * ‖g x‖)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, ← one_add_mul, ← mul_assoc]
  gcongr
  simpa using add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg x) k

private noncomputable def freqBand (m θ : 𝓢(ℝ,ℂ)) (j : ℤ) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ((θ.compSubConstCLM ℂ (j:ℝ)).hasTemperateGrowth) m

private lemma freqBand_apply (m θ : 𝓢(ℝ,ℂ)) (j : ℤ) (x : ℝ) :
    freqBand m θ j x = m x * θ (x-j) := rfl

private lemma makeFrequencyOperator {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (horbit : ∀ u, Continuous (fun y => U y u))
    (hU : ∀ y, ‖U y‖ ≤ B * (1+|y|)^k) (m : 𝓢(ℝ,ℂ)) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, (𝓕⁻ (⇑m)) y • U y u) ∧
      ‖T‖ ≤ B * (∫ y : ℝ, (1+|y|)^k * ‖(𝓕⁻ (⇑m)) y‖) ∧
      ∀ (ξ : ℝ) (v : H), (∀ y : ℝ, U y v = Complex.exp (↑(-2*Real.pi*y*ξ) * Complex.I) • v) →
        T v = m ξ • v := by
  let g : 𝓢(ℝ,ℂ) := 𝓕⁻ m
  have hcoe : (⇑g : ℝ → ℂ) = 𝓕⁻ (⇑m) := SchwartzMap.fourierInv_coe m
  have hK : AEStronglyMeasurable (𝓕⁻ (⇑m)) := hcoe ▸ g.continuous.aestronglyMeasurable
  have hw : Integrable (fun x : ℝ => ‖(𝓕⁻ (⇑m)) x‖ * (1+|x|)^k) := by
    simpa only [mul_comm (‖_‖), ← hcoe] using schwartz_weighted_integral g k
  obtain ⟨T,hT,hb⟩ := integratedOperator_exists U (𝓕⁻ (⇑m)) (fun y : ℝ => (1+|y|)^k) B
    horbit hK hw (fun y => by positivity) hB hU
  refine ⟨T, hT, ?_, ?_⟩
  · simpa only [mul_comm (‖_‖)] using hb
  · intro ξ v hv
    apply integratedOperator_inverseFourier U m T m.integrable _ hT ξ m.continuous.continuousAt v hv
    simpa only [← SchwartzMap.fourier_coe] using (𝓕 m : 𝓢(ℝ,ℂ)).integrable


open scoped Topology
namespace LocalizedFourier

/-- The same five possible integer bands suffice near a given frequency for every jet order. -/
theorem finite_jet_reconstruction (m θ : 𝓢(ℝ,ℂ))
    (hz : ∀ t : ℝ, 1 ≤ |t| → θ t = 0)
    (hp : ∀ t : ℝ, HasSum (fun j : ℤ => θ (t-(j:ℝ))) 1) (x : ℝ) :
    ∃ S : Finset ℤ, ∀ r : ℕ,
      (∀ j ∉ S, iteratedDeriv r (fun t : ℝ => m t * θ (t-(j:ℝ))) x = 0) ∧
      (∑ j ∈ S, iteratedDeriv r (fun t : ℝ => m t * θ (t-(j:ℝ))) x) = iteratedDeriv r m x := by
  let p := ⌊x⌋
  let S := Finset.Icc (p-2) (p+2)
  let b := fun (j : ℤ) (t : ℝ) => m t * θ (t-(j:ℝ))
  have hnear : Set.Ioo ((p:ℝ)-1) ((p:ℝ)+2) ∈ 𝓝 x :=
    Ioo_mem_nhds (by linarith [show (p:ℝ) ≤ x from Int.floor_le x])
      (by linarith [show x < (p:ℝ)+1 from Int.lt_floor_add_one x])
  have hθ (t : ℝ) (ht : t ∈ Set.Ioo ((p:ℝ)-1) ((p:ℝ)+2)) (j : ℤ) (hj : j ∉ S) :
      θ (t-(j:ℝ)) = 0 := by
    apply hz
    simp only [S, Finset.mem_Icc, not_and_or, not_le] at hj
    rcases hj with hj | hj
    · have ha : (j:ℝ) < (p:ℝ)-2 := by exact_mod_cast hj
      exact le_abs.mpr (Or.inl (by linarith [ht.1]))
    · have ha : (p:ℝ)+3 ≤ (j:ℝ) := by exact_mod_cast (show p+3 ≤ j by omega)
      exact le_abs.mpr (Or.inr (by linarith [ht.2]))
  refine ⟨S, fun r => ⟨fun j hj => ?_, ?_⟩⟩
  · have he : b j =ᶠ[𝓝 x] (fun _ => (0:ℂ)) := by
      filter_upwards [hnear] with t ht
      simp [b, hθ t ht j hj]
    simpa [b] using he.iteratedDeriv_eq r
  · have he : (fun t => ∑ j ∈ S, b j t) =ᶠ[𝓝 x] m := by
      filter_upwards [hnear] with t ht
      have hsum : HasSum (fun j : ℤ => θ (t-(j:ℝ))) (∑ j ∈ S, θ (t-(j:ℝ))) :=
        hasSum_sum_of_ne_finset_zero (hθ t ht)
      simp only [b, ← Finset.mul_sum, hsum.unique (hp t), mul_one]
    have hbd (j : ℤ) : ContDiffAt ℝ r (b j) x :=
      (m.contDiffAt _).mul (((θ.smooth r).comp (contDiff_id.sub contDiff_const)).contDiffAt)
    simpa only [iteratedDeriv_fun_sum (fun j _ => hbd j)] using he.iteratedDeriv_eq r

/-- The moments of the inverse transform of a Schwartz function give its frequency jets,
with Fourier character exp(-2πi ξt). -/
theorem kernel_moment_eq_jet (b : 𝓢(ℝ,ℂ)) (r : ℕ) (ξ : ℝ) :
    iteratedDeriv r b ξ = ((-2:ℂ) * Real.pi * Complex.I)^r *
      ∫ t : ℝ, (t:ℂ)^r * Complex.exp ((↑(-2 * Real.pi * (ξ*t)) : ℂ) * Complex.I) *
        (𝓕⁻ (b : ℝ → ℂ)) t := by
  let f : 𝓢(ℝ,ℂ) := 𝓕⁻ b
  have hi (a : ℕ) : Integrable (fun t : ℝ => t^a • f t) := by
    apply (f.integrable_pow_mul volume a).mono' (by fun_prop)
    exact Eventually.of_forall fun t => by simp
  have h := congrFun (Real.iteratedDeriv_fourier (f:=(f:ℝ→ℂ)) (N:=(r:ℕ∞))
    (fun a _ => hi a) (le_rfl : (r:ℕ∞) ≤ r)) ξ
  have he : 𝓕 (f:ℝ→ℂ) = (b:ℝ→ℂ) := by
    rw [← SchwartzMap.fourier_coe]
    simp [f]
  rw [he, Real.fourier_eq'] at h
  rw [← integral_const_mul]
  change iteratedDeriv r b ξ = ∫ t : ℝ, _ * (_ * _ * ((𝓕⁻ (b:ℝ→ℂ)) t))
  apply h.trans
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  simp only [Real.inner_apply, smul_eq_mul, ← SchwartzMap.fourierInv_coe]
  dsimp [f]
  rw [mul_pow]
  rw [mul_comm t ξ]
  ring

end LocalizedFourier

open scoped Topology

theorem jet_band_count {ι : Type*} (d : ι → ℕ) (ν : ι → ℝ)
    (hw : Summable (fun i => (d i : ℝ)/(1+(ν i)^2))) :
    ∃ F : ℤ → Finset ι, ∃ G : ℤ → Finset (Σ i, Fin (d i)), ∃ C : ℝ, 0 ≤ C ∧
    (∀ j i, 0 < d i → (i ∈ F j ↔ |ν i-j| ≤ 1)) ∧
    (∀ j, (G j).card = ∑ i ∈ F j, d i) ∧
    ∀ j, ((G j).card : ℝ) ≤ C * (1+|(j:ℝ)|)^2 := by
  classical
  have hs : Summable (fun p : Σ i, Fin (d i) => 1 / (1+(ν p.1)^2)) := by
    apply (summable_sigma_of_nonneg (fun _ => by positivity)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa [tsum_fintype, div_eq_mul_inv] using hw
  obtain ⟨G,C,hC,hm,hc⟩ := polynomial_band_count (fun p : Σ i, Fin (d i) => ν p.1) hs
  let F (j : ℤ) := (G j).image Sigma.fst
  have hF (j : ℤ) (i : ι) (hi : 0 < d i) : i ∈ F j ↔ |ν i-j| ≤ 1 := by
    constructor
    · intro h
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
      exact (hm j p).mp hp
    · intro h
      exact Finset.mem_image.mpr ⟨⟨i,⟨0,hi⟩⟩,(hm j _).mpr h,rfl⟩
  refine ⟨F,G,C,hC,hF,fun j => ?_,hc⟩
  have h : G j = (F j).sigma (fun i => (Finset.univ : Finset (Fin (d i)))) := by
    ext ⟨i,s⟩
    simp only [hm, Finset.mem_sigma, Finset.mem_univ, and_true, hF j i (Nat.zero_lt_of_lt s.isLt)]
  rw [h, Finset.card_sigma]
  simp

noncomputable def jetCoef (b : 𝓢(ℝ,ℂ)) (ξ : ℝ) (r s : ℕ) : ℂ :=
  (r.choose s : ℂ) * (iteratedDeriv (r-s) b ξ / ((-2:ℂ)*Real.pi*Complex.I)^(r-s))

theorem jetCoef_self (b : 𝓢(ℝ,ℂ)) (ξ : ℝ) (r : ℕ) : jetCoef b ξ r r = b ξ := by simp [jetCoef]

theorem jet_operator_action {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {d : ℕ} (v : Fin d → H) (ν : ℝ) (U : ℝ → H →L[ℂ] H) (b : 𝓢(ℝ,ℂ)) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, (𝓕⁻ (b : ℝ → ℂ)) y • U y u)
    (hU : ∀ (r : Fin d) (y : ℝ), U y (v r) =
      Complex.exp (↑(-2*Real.pi*y*ν) * Complex.I) •
        ∑ s ∈ Finset.Iic r, ((r.val.choose s.val : ℂ) * (y:ℂ)^(r.val-s.val)) • v s)
    (r : Fin d) : T (v r) = ∑ s ∈ Finset.Iic r, jetCoef b ν r.val s.val • v s := by
  let K : 𝓢(ℝ,ℂ) := 𝓕⁻ b
  let e := fun y : ℝ => Complex.exp (↑(-2 * Real.pi * (ν*y)) * Complex.I)
  let moment := fun (a : ℕ) (y : ℝ) => (y:ℂ)^a * e y * K y
  have hmoment (a : ℕ) : Integrable (moment a) := by
    refine (K.integrable_pow_mul volume a).mono' (by dsimp [moment,e]; fun_prop) ?_
    exact Eventually.of_forall fun t => by
      simp only [moment,e,norm_mul,norm_pow,Complex.norm_real,Complex.norm_exp_ofReal_mul_I,mul_one,le_refl]
  have hI (a : ℕ) : ∫ y : ℝ, moment a y = iteratedDeriv a b ν / ((-2:ℂ)*Real.pi*Complex.I)^a := by
    apply (eq_div_iff (pow_ne_zero _ (by simp [Real.pi_ne_zero]))).mpr
    rw [mul_comm]
    simpa only [moment,e,K,SchwartzMap.fourierInv_coe] using (LocalizedFourier.kernel_moment_eq_jet b a ν).symm
  have he (y : ℝ) : Complex.exp (↑(-2*Real.pi*y*ν) * Complex.I) = e y := by
    dsimp [e]
    congr 3; ring
  have hfun (y : ℝ) : (𝓕⁻ (b : ℝ→ℂ)) y • U y (v r) =
      ∑ s ∈ Finset.Iic r, ((r.val.choose s.val : ℂ) * moment (r.val-s.val) y) • v s := by
    rw [hU, he, ← SchwartzMap.fourierInv_coe, Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun s _ => by
      simp only [smul_smul,moment,K]
      congr 1
      ring)
  rw [hT]
  simp_rw [hfun]
  rw [integral_finsetSum _ (fun s _ => ((hmoment _).const_mul (r.val.choose s.val : ℂ)).smul_const (v s))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_smul_const, integral_const_mul, hI, jetCoef]

theorem jetCoef_local_zero (m θ : 𝓢(ℝ,ℂ)) (hz : ∀ t : ℝ, 1 ≤ |t| → θ t = 0)
    (j : ℤ) (ξ : ℝ) (hx : 1 < |ξ-(j:ℝ)|) (r s : ℕ) : jetCoef (freqBand m θ j) ξ r s = 0 := by
  have hnear : ∀ᶠ z in 𝓝 ξ, 1 < |z-(j:ℝ)| :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).mem_nhds hx
  have he : (freqBand m θ j : ℝ → ℂ) =ᶠ[𝓝 ξ] (fun _ => (0:ℂ)) := by
    filter_upwards [hnear] with z ht
    simp [freqBand_apply, hz _ ht.le]
  have h := he.iteratedDeriv_eq (r-s)
  simp only [iteratedDeriv_fun_const_zero] at h
  simp [jetCoef,h]

theorem jetCoef_reconstruction (m θ : 𝓢(ℝ,ℂ)) (hz : ∀ t : ℝ, 1 ≤ |t| → θ t = 0)
    (hp : ∀ t : ℝ, HasSum (fun j : ℤ => θ (t-(j:ℝ))) 1) (ξ : ℝ) (r s : ℕ) :
    HasSum (fun j : ℤ => jetCoef (freqBand m θ j) ξ r s) (jetCoef m ξ r s) := by
  obtain ⟨S,hS⟩ := LocalizedFourier.finite_jet_reconstruction m θ hz hp ξ
  have h : HasSum (fun j : ℤ => iteratedDeriv (r-s) (freqBand m θ j) ξ) (iteratedDeriv (r-s) m ξ) := by
    rw [← (hS (r-s)).2]
    exact hasSum_sum_of_ne_finset_zero (hS (r-s)).1
  simpa only [jetCoef,div_eq_mul_inv] using (h.mul_right (((-2:ℂ)*Real.pi*Complex.I)^(r-s))⁻¹).mul_left (r.choose s:ℂ)

theorem MasulloRH.spectral_trace_of_polynomial_translation_jets {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (horbit : ∀ u, Continuous (fun y => U y u))
    (hU : ∀ y, ‖U y‖ ≤ B * (1+|y|)^k)
    (d : ι → ℕ) (v : (Σ i, Fin (d i)) → H) (ν : ι → ℝ)
    (hl : LinearIndependent ℂ v) (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (hjet : ∀ i (r : Fin (d i)) (y : ℝ), U y (v ⟨i,r⟩) =
      Complex.exp (↑(-2*Real.pi*y*ν i) * Complex.I) •
        ∑ s ∈ Finset.Iic r, ((r.val.choose s.val : ℂ) * (y:ℂ)^(r.val-s.val)) • v ⟨i,s⟩)
    (hw : Summable (fun i => (d i:ℝ)/(1+(ν i)^2))) (m : 𝓢(ℝ,ℂ)) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, (𝓕⁻ (m : ℝ→ℂ)) y • U y u) ∧
      IsNuclearOperator T ∧ HasSum (fun i => (d i:ℂ) * m (ν i)) (operatorTrace T) := by
  classical
  obtain ⟨T,hT,_,_⟩ := makeFrequencyOperator U k B hB horbit hU m
  have ht i := jet_operator_action (fun r : Fin (d i) => v ⟨i,r⟩) (ν i) U m T hT (hjet i)
  refine ⟨T,hT,?_⟩
  let θ := LocalizedFourier.integerWindow
  let b := freqBand m θ
  obtain ⟨F,G,C,hC,hF,hcard,hcount⟩ := jet_band_count d ν hw
  choose A hA hnorm _ using fun j : ℤ => makeFrequencyOperator U k B hB horbit hU (b j)
  have ha j i := jet_operator_action (fun r : Fin (d i) => v ⟨i,r⟩) (ν i) U (b j) (A j) (hA j) (hjet i)
  obtain ⟨L,_,hkernel⟩ := localized_fourier_multiplier m θ k 4
  have hdecay (j : ℤ) : (1+|(j:ℝ)|)^4 * ‖A j‖ ≤ B * L := by
    calc
      _ ≤ (1+|(j:ℝ)|)^4 * (B * (∫ y : ℝ, (1+|y|)^k *
          ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-(j:ℝ)))) y‖)) :=
        mul_le_mul_of_nonneg_left (hnorm j) (by positivity)
      _ = B * ((1+|(j:ℝ)|)^4 * (∫ y : ℝ, (1+|y|)^k *
          ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-(j:ℝ)))) y‖)) := by ring
      _ ≤ B*L := mul_le_mul_of_nonneg_left (hkernel j).2 hB
  have hc := summable_band_cost A G C (B*L) hC hcount hdecay
  let e := Equiv.intEquivNat.symm
  refine trace_of_triangular_frequency_bands d v hl hd (fun n => F (e n)) (fun n => A (e n))
    (fun n i => b (e n) (ν i)) (fun n i r s => jetCoef (b (e n)) (ν i) r.val s.val) ?_ ?_ ?_ T
    (fun i => m (ν i)) ?_ ?_
  · intro n i r
    rw [ha, Finset.Iic_eq_cons_Iio, Finset.sum_cons, jetCoef_self]
  · intro n i hi r
    have hξ : 1 < |ν i - (e n:ℝ)| := lt_of_not_ge (fun h => hi ((hF _ _ (Nat.zero_lt_of_lt r.isLt)).mpr h))
    rw [ha]
    exact Finset.sum_eq_zero (fun s _ => by
      simp only [b, jetCoef_local_zero m θ LocalizedFourier.integerWindow_zero (e n) _ hξ, zero_smul])
  · exact (e.summable_iff (f:=fun j : ℤ => (↑(∑ i ∈ F j, d i) : ℝ) * ‖A j‖)).mpr
      (by simpa only [hcard] using hc)
  · intro i _
    have hscalar : HasSum (fun j : ℤ => b j (ν i)) (m (ν i)) := by
      change HasSum (fun j : ℤ => m (ν i) * θ (ν i - (j:ℝ))) (m (ν i))
      simpa only [mul_one] using (LocalizedFourier.integerWindow_hasSum (ν i)).mul_left (m (ν i))
    exact (e.hasSum_iff (f:=fun j : ℤ => b j (ν i))).mpr hscalar
  · rintro ⟨i,r⟩
    have hvec : HasSum (fun j : ℤ => A j (v ⟨i,r⟩)) (T (v ⟨i,r⟩)) := by
      simp only [ha,ht]
      apply hasSum_sum (f:=fun (s : Fin (d i)) (j : ℤ) => jetCoef (b j) (ν i) r.val s.val • v ⟨i,s⟩)
      intro s _
      exact (jetCoef_reconstruction m θ LocalizedFourier.integerWindow_zero LocalizedFourier.integerWindow_hasSum
        (ν i) r.val s.val).smul_const (v ⟨i,s⟩)
    exact (e.hasSum_iff (f:=fun j : ℤ => A j (v ⟨i,r⟩))).mpr hvec
end

section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace MasulloRH
noncomputable section

abbrev LogL2 := Lp ℂ 2 (volume : Measure ℝ)

def logWeight (p x : ℝ) : ℝ := (1 + |x|) ^ (-p)

lemma logWeight_pos (p x : ℝ) : 0 < logWeight p x := Real.rpow_pos_of_pos (by positivity) _

lemma continuous_logWeight (p : ℝ) : Continuous (logWeight p) := by
  apply Continuous.rpow_const (continuous_const.add continuous_abs)
  exact fun x => Or.inl (show (1 + |x| : ℝ) ≠ 0 by positivity)

lemma logWeight_ratio_le {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    logWeight p x / logWeight p (x+y) ≤ (1 + |y|)^p := by
  have hx : 0 < 1 + |x| := by positivity
  have hxy : 0 < 1 + |x+y| := by positivity
  have hab : 1 + |x+y| ≤ (1 + |x|) * (1 + |y|) := by
    nlinarith [abs_add_le x y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]
  rw [logWeight, logWeight, Real.rpow_neg hx.le, Real.rpow_neg hxy.le, inv_div_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx p)).2
  rw [mul_comm, ← Real.mul_rpow hx.le (show 0 ≤ 1 + |y| by positivity)]
  exact Real.rpow_le_rpow hxy.le hab hp

private def ratio (p y x : ℝ) : ℂ := (logWeight p x / logWeight p (x+y) : ℝ)

private lemma ratio_norm (p y x : ℝ) : ‖ratio p y x‖ = logWeight p x / logWeight p (x+y) := by
  exact Complex.norm_of_nonneg (div_nonneg (logWeight_pos _ _).le (logWeight_pos _ _).le)

private lemma ratio_mem (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : MemLp (ratio p y) ⊤ volume := by
  apply memLp_top_of_bound _ ((1+|y|)^p) (ae_of_all _ fun x => (ratio_norm p y x).le.trans (logWeight_ratio_le hp x y))
  apply Continuous.aestronglyMeasurable
  exact Complex.continuous_ofReal.comp <| (continuous_logWeight p).div
    ((continuous_logWeight p).comp (continuous_id.add_const y)) (fun x => (logWeight_pos _ _).ne')

private def shift (y : ℝ) : LogL2 →ₗᵢ[ℂ] LogL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x+y) (measurePreserving_add_right volume y)

def weightedTranslation (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : LogL2 →L[ℂ] LogL2 :=
  (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) ((ratio_mem p hp y).toLp (ratio p y))).comp
    (shift y).toContinuousLinearMap

lemma weightedTranslation_apply_ae (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : LogL2) :
    (weightedTranslation p hp y f : ℝ → ℂ) =ᵐ[volume] fun x =>
      ((logWeight p x / logWeight p (x+y) : ℝ) : ℂ) * f (x+y) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((ratio_mem p hp y).toLp (ratio p y)) (shift y f)
  have hs := Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)
  refine h.trans ?_
  filter_upwards [(ratio_mem p hp y).coeFn_toLp, hs] with x hx hsx
  change ((ratio_mem p hp y).toLp (ratio p y)) x * (shift y f) x = _
  change (shift y f) x = f (x+y) at hsx
  rw [hx, hsx]; rfl

lemma norm_weightedTranslation_le (p : ℝ) (hp : 0 ≤ p) (y : ℝ) :
    ‖weightedTranslation p hp y‖ ≤ (1+|y|)^p := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [← (shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedTranslation_apply_ae p hp y f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hs
  change (shift y f) x = f (x+y) at hs
  rw [hx, hs, norm_mul]
  exact mul_le_mul_of_nonneg_right ((ratio_norm p y x).le.trans (logWeight_ratio_le hp x y)) (norm_nonneg _)

lemma weightedTranslation_zero (p : ℝ) (hp : 0 ≤ p) : weightedTranslation p hp 0 = .id ℂ LogL2 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [weightedTranslation_apply_ae p hp 0 f] with x h
  change (weightedTranslation p hp 0 f) x = f x
  simpa only [add_zero, div_self (logWeight_pos p x).ne', Complex.ofReal_one, one_mul] using h

lemma weightedTranslation_add (p : ℝ) (hp : 0 ≤ p) (y z : ℝ) :
    weightedTranslation p hp (y+z) = (weightedTranslation p hp y).comp (weightedTranslation p hp z) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hz := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp
    (weightedTranslation_apply_ae p hp z f)
  filter_upwards [weightedTranslation_apply_ae p hp (y+z) f,
    weightedTranslation_apply_ae p hp y ((weightedTranslation p hp z) f), hz] with x hall hy hz
  change (weightedTranslation p hp z f) (x+y) = _ at hz
  change (weightedTranslation p hp (y+z) f) x = (weightedTranslation p hp y ((weightedTranslation p hp z) f)) x
  rw [hall, hy, hz]
  simp only [Function.comp_apply, ← add_assoc, ← mul_assoc, ← Complex.ofReal_mul]
  field_simp [ne_of_gt (logWeight_pos p (x+y)), ne_of_gt (logWeight_pos p (x+y+z))]

def angularCharacter (ξ x : ℝ) : ℂ := Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)

lemma angularCharacter_add (ξ x y : ℝ) :
    angularCharacter ξ (x+y) = angularCharacter ξ x * angularCharacter ξ y := by
  simp [angularCharacter, mul_add, add_mul, Complex.exp_add]

lemma norm_angularCharacter (ξ x : ℝ) : ‖angularCharacter ξ x‖ = 1 := by
  simp [angularCharacter, Complex.norm_exp]

lemma weightedExponential_memLp (p ξ : ℝ) (hp : 1/2 < p) :
    MemLp (fun x : ℝ => (logWeight p x : ℂ) * angularCharacter ξ x) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm _).2
  · have hdeg : (Module.finrank ℝ ℝ : ℝ) < 2*p := by simp; linarith
    have hint := integrable_one_add_norm (E := ℝ) (μ := volume) hdeg
    apply hint.congr
    apply Filter.Eventually.of_forall
    intro x
    change (1 + ‖x‖)^(-(2*p)) = ‖(logWeight p x : ℂ) * angularCharacter ξ x‖^2
    rw [norm_mul, norm_angularCharacter, mul_one, Complex.norm_of_nonneg (logWeight_pos _ _).le,
      logWeight, ← Real.rpow_mul_natCast (by positivity)]
    simp [Real.norm_eq_abs, mul_comm]
  · apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (continuous_logWeight p)).mul
      (show Continuous (angularCharacter ξ) by unfold angularCharacter; fun_prop)

private lemma ratio_sub_one_bound {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    |logWeight p x / logWeight p (x+y) - 1| ≤ (1+|y|)^p - 1 := by
  let a := logWeight p x / logWeight p (x+y)
  let D := (1+|y|)^p
  have hD : 1 ≤ D := Real.one_le_rpow (by linarith [abs_nonneg y]) hp
  have ha : a ≤ D := logWeight_ratio_le hp x y
  have hinv := logWeight_ratio_le hp (x+y) (-y)
  simp only [add_neg_cancel_right, abs_neg] at hinv
  have hDa : 1 ≤ D*a := by
    change 1 ≤ D * (logWeight p x / logWeight p (x+y))
    rw [← mul_div_assoc, le_div_iff₀ (logWeight_pos p (x+y)), one_mul]
    exact (div_le_iff₀ (logWeight_pos p x)).mp hinv
  change |a-1| ≤ D-1
  apply abs_le.mpr
  refine ⟨?_, by linarith⟩
  by_cases h : a ≤ 1
  · have h' := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hD)
    nlinarith
  · linarith

private lemma shift_continuous (f : LogL2) : Continuous (fun y : ℝ => shift y f) := by
  let g : C(ℝ × ℝ, ℝ) := ⟨fun z => z.2 + z.1, continuous_snd.add continuous_fst⟩
  exact continuous_const.compMeasurePreservingLp (g := g.curry) g.curry.continuous
    (fun y => measurePreserving_add_right volume y) (by norm_num)

private lemma diff_shift_bound (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : LogL2) :
    ‖weightedTranslation p hp y f - shift y f‖ ≤ ((1+|y|)^p-1) * ‖f‖ := by
  rw [← (shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedTranslation_apply_ae p hp y f,
    Lp.coeFn_sub (weightedTranslation p hp y f) (shift y f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hsub hs
  change (shift y f) x = f (x+y) at hs
  rw [hsub, Pi.sub_apply, hx, hs, ← sub_one_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact ratio_sub_one_bound hp x y

lemma continuous_weightedTranslation_orbit (p : ℝ) (hp : 0 ≤ p) (f : LogL2) :
    Continuous (fun y : ℝ => weightedTranslation p hp y f) := by
  have hlim : Tendsto (fun y : ℝ => weightedTranslation p hp y f) (𝓝 0) (𝓝 f) := by
    have hg : Continuous (fun y : ℝ => ((1+|y|)^p-1) * ‖f‖) := by
      apply Continuous.mul_const
      apply Continuous.sub _ continuous_const
      apply Continuous.rpow_const (continuous_const.add continuous_abs)
      exact fun x => Or.inl (show (1 + |x| : ℝ) ≠ 0 by positivity)
    have hbound : Tendsto (fun y : ℝ => ((1+|y|)^p-1) * ‖f‖) (𝓝 0) (𝓝 0) := by
      simpa using hg.tendsto 0
    have hdiff : Tendsto (fun y : ℝ => weightedTranslation p hp y f - shift y f) (𝓝 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => norm_nonneg _) (fun y => diff_shift_bound p hp y f) hbound
    have hs0 : shift 0 f = f := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (0:ℝ))] with x hx
      change (shift 0 f) x = f (x+0) at hx
      simpa only [add_zero] using hx
    have hs := (shift_continuous f).tendsto 0
    rw [hs0] at hs
    simpa only [sub_add_cancel, zero_add] using hdiff.add hs
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : Tendsto (fun z : ℝ => z-y) (𝓝 y) (𝓝 0) := by simpa using (show Continuous (fun z : ℝ => z-y) from continuous_id.sub continuous_const).tendsto y
  have h := (weightedTranslation p hp y).continuous.continuousAt.tendsto.comp (hlim.comp hd)
  refine h.congr fun z => ?_
  change (weightedTranslation p hp y) ((weightedTranslation p hp (z-y)) f) = _
  rw [← ContinuousLinearMap.comp_apply, ← weightedTranslation_add]
  simp

end
end MasulloRH
end

section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Polynomial
namespace MasulloRH
noncomputable section

private def jetSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)))
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  smul_mem' := by
    intro c f hf
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => c)).smul (show ContDiff ℝ ∞ f from hf)

private lemma jet_smooth (f : jetSpace) : ContDiff ℝ ∞ f.val := f.property

private def jetDeriv : Module.End ℂ jetSpace where
  toFun f := ⟨deriv f.val, by
    change ContDiff ℝ ∞ (deriv _)
    apply ContDiff.deriv'
    simpa using jet_smooth f⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact deriv_add ((jet_smooth f).differentiable (by simp) x) ((jet_smooth g).differentiable (by simp) x)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact deriv_const_smul c ((jet_smooth f).differentiable (by simp) x)

private def jet (a : ℂ) (n : ℕ) : jetSpace :=
  ⟨fun x => (x:ℂ)^n * Complex.exp (a * x), by
    change ContDiff ℝ ∞ _
    have hc : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    exact (hc.pow n).mul ((Complex.contDiff_exp : ContDiff ℝ ∞ Complex.exp).comp (contDiff_const.mul hc))⟩

private theorem jet_deriv_sub (a : ℂ) (n : ℕ) :
    (jetDeriv - a • 1) (jet a n) = (n:ℂ) • jet a (n-1) := by
  apply Subtype.ext
  funext x
  change deriv (fun y : ℝ => (y:ℂ)^n * Complex.exp (a * y)) x -
    a * ((x:ℂ)^n * Complex.exp (a*x)) =
      (n:ℂ) * ((x:ℂ)^(n-1) * Complex.exp (a*x))
  have h : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := x))
  have hd := ((h.pow n).mul ((h.const_mul a).cexp)).deriv
  change deriv (fun y : ℝ => (y:ℂ)^n * Complex.exp (a * y)) x = _ at hd
  rw [hd]
  simp only [Pi.pow_apply]
  ring

private theorem jet_nilpotent (a : ℂ) (n : ℕ) :
    ((jetDeriv - a • 1) ^ (n+1)) (jet a n) = 0 := by
  induction n with
  | zero => rw [Nat.zero_add, pow_one, jet_deriv_sub]; simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, jet_deriv_sub, map_smul]
    simp [ih]

private def jetPolynomial (a : ℂ) : ℂ[X] →ₗ[ℂ] (ℝ → ℂ) where
  toFun P x := P.eval (x:ℂ) * Complex.exp (a * x)
  map_add' P Q := by ext x; simp [add_mul]
  map_smul' c P := by ext x; simp [mul_assoc]

private theorem jetPolynomial_injective (a : ℂ) : Function.Injective (jetPolynomial a) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro P hP
  apply P.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro _ ⟨x, rfl⟩
  have h := congrFun hP x
  exact (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)

private theorem jet_layer_independent (a : ℂ) : LinearIndependent ℂ (jet a) := by
  apply LinearIndependent.of_comp jetSpace.subtype
  have hb := (Polynomial.basisMonomials ℂ).linearIndependent.map' (jetPolynomial a)
    (LinearMap.ker_eq_bot.mpr (jetPolynomial_injective a))
  change LinearIndependent ℂ (fun n => fun x : ℝ => (x:ℂ)^n * Complex.exp (a*x))
  simpa only [Polynomial.coe_basisMonomials, Function.comp_def, jetPolynomial, LinearMap.coe_mk,
    AddHom.coe_mk, Polynomial.eval_monomial, one_mul] using hb

theorem polynomialExponentialJets_independent :
    LinearIndependent ℂ (fun i : ℂ × ℕ => fun x : ℝ => (x : ℂ) ^ i.2 * Complex.exp (i.1 * x)) := by
  have hm : ∀ a, Submodule.span ℂ (Set.range (jet a)) ≤ jetDeriv.maxGenEigenspace a := by
    intro a
    rw [Submodule.span_le]
    rintro _ ⟨n,rfl⟩
    exact (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨n+1, jet_nilpotent a n⟩
  have hs := jetDeriv.independent_maxGenEigenspace.mono hm
  have hSigma := linearIndependent_iUnion_finite jet_layer_independent
    (fun _ _ _ h => hs.disjoint_biSup h)
  have hprod := hSigma.comp (fun i : ℂ × ℕ => (⟨i.1,i.2⟩ : Σ _ : ℂ, ℕ)) (by
    intro a b h
    have h₁ := congrArg Sigma.fst h
    have h₂ := congrArg (fun i : Σ _ : ℂ, ℕ => i.2) h
    exact Prod.ext h₁ h₂)
  exact hprod.map' jetSpace.subtype (LinearMap.ker_eq_bot.mpr jetSpace.injective_subtype)

open MeasureTheory Filter

theorem linearIndependent_weightedLp_of_continuous {ι : Type*}
    (F : ι → ℝ → ℂ) (hF : ∀ i, Continuous (F i)) (hI : LinearIndependent ℂ F)
    (w : ℝ → ℂ) (hw : ∀ᵐ x ∂volume, w x ≠ 0) (u : ι → Lp ℂ 2 (volume : Measure ℝ))
    (hu : ∀ i, u i =ᵐ[volume] fun x => w x * F i x) : LinearIndependent ℂ u := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc
  have hsum (S : Finset ι) :
      (↑(∑ i ∈ S, c i • u i) : ℝ → ℂ) =ᵐ[volume]
        fun x => w x * ∑ i ∈ S, c i * F i x := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, mul_zero]
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
      exact hx
    | insert i S hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • u i) (∑ j ∈ S, c j • u j), Lp.coeFn_smul (c i) (u i),
        hu i, ih] with x h₁ h₂ h₃ h₄
      rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, smul_eq_mul, h₃, h₄, Finset.sum_insert hi]
      ring
  have hzero : (fun x => ∑ i ∈ s, c i * F i x) =ᵐ[volume] fun _ => 0 := by
    have h := hsum s
    rw [hc] at h
    filter_upwards [h, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ), hw] with x hx hz hwx
    rw [hz] at hx
    exact (mul_eq_zero.mp hx.symm).resolve_left hwx
  have hpoint := Measure.eq_of_ae_eq hzero (continuous_finsetSum _ fun i _ => continuous_const.mul (hF i)) continuous_const
  apply linearIndependent_iff'.mp hI s c
  funext x
  simpa using congrFun hpoint x

theorem weightedPolynomialExponentialJets_independent {ι : Type*}
    (a : ι → ℂ × ℕ) (ha : Function.Injective a)
    (w : ℝ → ℂ) (hw : ∀ᵐ x ∂volume, w x ≠ 0)
    (u : ι → Lp ℂ 2 (volume : Measure ℝ))
    (hu : ∀ i, u i =ᵐ[volume] fun x => w x * ((x:ℂ)^(a i).2 * Complex.exp ((a i).1*x))) :
    LinearIndependent ℂ u := by
  exact linearIndependent_weightedLp_of_continuous
    (fun i x => (x:ℂ)^(a i).2 * Complex.exp ((a i).1*x))
    (fun _ => by fun_prop) (polynomialExponentialJets_independent.comp a ha) w hw u hu

end
end MasulloRH
end

section
open MeasureTheory Set Filter
namespace MasulloRH
noncomputable section

theorem weightedAngularJet_memLp (p ξ : ℝ) (n : ℕ) (hp : (n:ℝ) + 1/2 < p) :
    MemLp (fun x : ℝ => (logWeight p x : ℂ) * ((x:ℂ)^n * angularCharacter ξ x)) 2 volume := by
  apply (weightedExponential_memLp (p-n) ξ (by linarith)).of_le
  · apply Continuous.aestronglyMeasurable
    have hw := Complex.continuous_ofReal.comp (continuous_logWeight p)
    have he : Continuous (angularCharacter ξ) := by unfold angularCharacter; fun_prop
    exact hw.mul ((Complex.continuous_ofReal.pow n).mul he)
  · apply Eventually.of_forall
    intro x
    simp only [norm_mul, norm_angularCharacter, mul_one, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_of_nonneg (logWeight_pos _ _).le]
    calc
      _ ≤ logWeight p x * (1 + |x|)^n := by
        apply mul_le_mul_of_nonneg_left _ (logWeight_pos p x).le
        exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
      _ = _ := by
        rw [logWeight, logWeight, ← Real.rpow_natCast, ← Real.rpow_add (by positivity : 0 < 1+|x|)]
        congr 1
        ring

def weightedAngularJet (p ξ : ℝ) (n : ℕ) (hp : (n:ℝ) + 1/2 < p) : LogL2 :=
  (weightedAngularJet_memLp p ξ n hp).toLp _

theorem linearIndependent_weightedAngularJets (p : ℝ) :
    LinearIndependent ℂ (fun i : {j : ℝ × ℕ // (j.2:ℝ) + 1/2 < p} =>
      weightedAngularJet p i.val.1 i.val.2 i.prop) := by
  let a (i : {j : ℝ × ℕ // (j.2:ℝ) + 1/2 < p}) : ℂ × ℕ := ((i.val.1:ℂ) * Complex.I, i.val.2)
  have ha : Function.Injective a := by
    intro i j h
    apply Subtype.ext
    apply Prod.ext
    · apply Complex.ofReal_injective
      apply mul_right_cancel₀ Complex.I_ne_zero
      exact congrArg Prod.fst h
    · exact congrArg (fun b : ℂ × ℕ => b.2) h
  apply weightedPolynomialExponentialJets_independent a ha (fun x => (logWeight p x : ℂ))
    (Eventually.of_forall (fun x => Complex.ofReal_ne_zero.mpr (logWeight_pos p x).ne'))
  intro i
  filter_upwards [(weightedAngularJet_memLp p i.val.1 i.val.2 i.prop).coeFn_toLp] with x hx
  change weightedAngularJet p i.val.1 i.val.2 i.prop x = _ at hx ⊢
  rw [hx]
  dsimp only [a, angularCharacter]
  congr 3
  ring

end
end MasulloRH
end

section
open Set Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology

namespace MasulloRH

abbrev CriticalLineZero := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1 / 2}

theorem criticalLineZero_scaled_multiplicity_summable :
    Summable (fun ρ : CriticalLineZero => (analyticOrderNatAt riemannZeta ρ.val : ℝ) /
        (1 + (-ρ.val.im / (2 * Real.pi)) ^ 2)) := by
  let e (ρ : CriticalLineZero) : ZetaZerosInTraceStrip 1 :=
    ⟨ρ.val, ρ.prop.1, by rw [ρ.prop.2]; norm_num, by rw [ρ.prop.2]; norm_num,
      by rw [ρ.prop.2]; norm_num⟩
  have he : Function.Injective e := fun _ _ h => Subtype.ext (congrArg (fun s : ZetaZerosInTraceStrip 1 => s.val) h)
  have hs := ((weighted_zero_summability 1 one_pos).comp_injective he).mul_left ((2 * Real.pi)^2)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro ρ
  let y := ρ.val.im
  let c := 2 * Real.pi
  have hc : 1 ≤ c := by dsimp [c]; linarith [Real.pi_gt_three]
  have hc0 : 0 < c := by linarith
  have hsc : 1 + y^2 ≤ c^2 * (1 + (-y/c)^2) := calc
    _ ≤ c^2 + y^2 := by nlinarith [sq_nonneg (c-1)]
    _ = _ := by field_simp
  have hrecip : 1 / (1 + (-y / c)^2) ≤ c^2 / (1+y^2) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa only [one_mul] using hsc)
  let m : ℝ := analyticOrderNatAt riemannZeta ρ.val
  have hm : 0 ≤ m := Nat.cast_nonneg _
  change m / (1 + (-y / c)^2) ≤ c^2 * (m / (1+y^2))
  calc
    _ = m * (1 / (1 + (-y / c)^2)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hrecip hm).trans_eq (by ring)

theorem exists_logTraceTest_schwartz (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ y, f y = φ (Real.exp y) := by
  have hk : IsCompact (Real.log '' tsupport φ) := hφ.2.1.image_of_continuousOn
    (Real.continuousOn_log.mono (fun x hx => ne_of_gt (hφ.2.2.1 hx)))
  have hc : HasCompactSupport (fun y => φ (Real.exp y)) :=
    HasCompactSupport.of_support_subset_isCompact hk (by
      intro y hy
      exact ⟨Real.exp y, subset_tsupport _ hy, Real.log_exp y⟩)
  exact ⟨hc.toSchwartzMap (hφ.1.comp Real.contDiff_exp), fun _ => rfl⟩

theorem fourier_logTraceTest_eq_mellin (φ : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun y : ℝ => φ (Real.exp y)) (-t / (2 * Real.pi)) = mellin φ (Complex.I * t) := by
  rw [mellin_eq_fourier]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, neg_zero, Real.exp_zero, one_smul,
    Complex.mul_im, one_mul, zero_add]
  rw [← Real.fourierInv_eq_fourier_comp_neg (fun y : ℝ => φ (Real.exp y))]
  rw [Real.fourierInv_eq_fourier_neg, neg_div]

end MasulloRH
end

section
open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH
noncomputable section

def zetaJetCount (p : ℝ) (ρ : CriticalLineZero) : ℕ :=
  min (analyticOrderNatAt riemannZeta ρ.val) ⌈p - 1/2⌉₊

abbrev ZetaJetIndex (p : ℝ) := Σ ρ : CriticalLineZero, Fin (zetaJetCount p ρ)

def zetaJetFrequency (ρ : CriticalLineZero) : ℝ := -ρ.val.im / (2 * Real.pi)

theorem zetaJetCount_summable (p : ℝ) :
    Summable (fun ρ => (zetaJetCount p ρ : ℝ) / (1 + (zetaJetFrequency ρ)^2)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ criticalLineZero_scaled_multiplicity_summable
  intro ρ
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast min_le_left (analyticOrderNatAt riemannZeta ρ.val) ⌈p-1/2⌉₊

theorem zetaJet_admissible {p : ℝ} (j : ZetaJetIndex p) : (j.2.val:ℝ) + 1/2 < p := by
  have h := Nat.lt_ceil.mp (j.2.isLt.trans_le (min_le_right _ _))
  linarith

def zetaJet (p : ℝ) (j : ZetaJetIndex p) : LogL2 :=
  weightedAngularJet p j.1.val.im j.2.val (zetaJet_admissible j)

theorem zetaJet_ae (p : ℝ) (j : ZetaJetIndex p) :
    (zetaJet p j : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      (logWeight p x : ℂ) * ((x:ℂ)^j.2.val * angularCharacter j.1.val.im x) :=
    (weightedAngularJet_memLp _ _ _ (zetaJet_admissible j)).coeFn_toLp

theorem zetaJet_independent (p : ℝ) : LinearIndependent ℂ (zetaJet p) := by
  let f (j : ZetaJetIndex p) : {i : ℝ × ℕ // (i.2:ℝ) + 1/2 < p} :=
    ⟨(j.1.val.im, j.2.val), zetaJet_admissible j⟩
  apply (linearIndependent_weightedAngularJets p).comp f
  rintro ⟨ρ,r⟩ ⟨σ,s⟩ h
  have hi := congrArg (fun i : {a : ℝ × ℕ // (a.2:ℝ) + 1/2 < p} => i.val.1) h
  have hj := congrArg (fun i : {a : ℝ × ℕ // (a.2:ℝ) + 1/2 < p} => i.val.2) h
  have he : ρ = σ := Subtype.ext (Complex.ext (ρ.prop.2.trans σ.prop.2.symm) hi)
  subst σ
  exact congrArg (Sigma.mk ρ) (Fin.ext hj)

private theorem lp_finsum_ae {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u : ι → LogL2) :
    (↑(∑ i ∈ s, c i • u i) : ℝ → ℂ) =ᵐ[volume] fun x => ∑ i ∈ s, c i * u i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx using hx
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (c i • u i) (∑ j ∈ s, c j • u j), Lp.coeFn_smul (c i) (u i),ih]
      with x ha hs h
    rw [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,h,Finset.sum_insert hi]

private theorem fin_binomial {d : ℕ} (r : Fin d) (x y : ℂ) :
    (x+y)^r.val = ∑ s ∈ Finset.Iic r, x^s.val * y^(r.val-s.val) * r.val.choose s.val := by
  rw [add_pow, Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic r, Finset.sum_map]
  rfl

theorem weightedShift_zetaJet (p : ℝ) (hp : 1/2 < p) (ρ : CriticalLineZero)
    (r : Fin (zetaJetCount p ρ)) (y : ℝ) :
    weightedTranslation p (by linarith) y (zetaJet p ⟨ρ,r⟩) = angularCharacter ρ.val.im y •
      ∑ s ∈ Finset.Iic r, ((r.val.choose s.val : ℂ) * (y:ℂ)^(r.val-s.val)) • zetaJet p ⟨ρ,s⟩ := by
  let c (s : Fin (zetaJetCount p ρ)) : ℂ := r.val.choose s.val * (y:ℂ)^(r.val-s.val)
  let u (s : Fin (zetaJetCount p ρ)) := zetaJet p ⟨ρ,s⟩
  have hs := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp (zetaJet_ae p ⟨ρ,r⟩)
  have hall := ae_all_iff.mpr (fun s : Fin (zetaJetCount p ρ) => zetaJet_ae p ⟨ρ,s⟩)
  apply Lp.ext
  filter_upwards [weightedTranslation_apply_ae p (by linarith) y (u r), hs, hall,
    lp_finsum_ae (Finset.Iic r) c u, Lp.coeFn_smul (angularCharacter ρ.val.im y) (∑ s ∈ Finset.Iic r, c s • u s)]
    with x hU hxy he hsum hmul
  change u r (x+y) = (logWeight p (x+y) : ℂ) * (↑(x+y)^r.val * angularCharacter ρ.val.im (x+y)) at hxy
  change weightedTranslation p _ y (u r) x = (angularCharacter ρ.val.im y • (∑ s ∈ Finset.Iic r, c s • u s) : LogL2) x
  rw [hU,hxy,hmul,Pi.smul_apply,smul_eq_mul,hsum,angularCharacter_add,Complex.ofReal_div,Complex.ofReal_add]
  have hq : (logWeight p x : ℂ) / (logWeight p (x+y) : ℂ) * (logWeight p (x+y) : ℂ) = (logWeight p x : ℂ) :=
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (logWeight_pos _ _).ne')
  rw [← mul_assoc, hq, fin_binomial, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change _ = _ * (_ * zetaJet p ⟨ρ,s⟩ x)
  rw [he s]
  dsimp [c]
  ring

end
end MasulloRH
end

section
open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH
noncomputable section

def paperWeight (p x : ℝ) := (1+x^2)^(-p/2)
theorem paperWeight_pos (p x : ℝ) : 0 < paperWeight p x := Real.rpow_pos_of_pos (by positivity) _
private theorem paperWeight_cont (p : ℝ) : Continuous (paperWeight p) := by
  unfold paperWeight
  exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))

private theorem weightRatio_upper {p : ℝ} (hp : 0 < p) (x : ℝ) :
    paperWeight p x / logWeight p x ≤ 2^(p/2) := by
  apply (div_le_iff₀ (logWeight_pos _ _)).mpr
  simpa only [paperWeight, logWeight, Real.norm_eq_abs, sq_abs] using rpow_neg_one_add_norm_sq_le x hp

private theorem weightRatio_lower {p : ℝ} (hp : 0 < p) (x : ℝ) :
    logWeight p x / paperWeight p x ≤ 1 := by
  rw [div_le_one (paperWeight_pos _ _), paperWeight, Real.rpow_div_two_eq_sqrt _ (by positivity)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hp.le)
  simpa only [Real.norm_eq_abs, sq_abs] using sqrt_one_add_norm_sq_le x

private def weightChange (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (C : ℝ) (hC : ∀ x, f x / g x ≤ C) : LogL2 →L[ℂ] LogL2 :=
  let v := fun x : ℝ => ((f x / g x : ℝ) : ℂ)
  let hv : MemLp v ⊤ volume := memLp_top_of_bound
      (Complex.continuous_ofReal.comp (hf.div hg (fun x => (hgp x).ne'))).aestronglyMeasurable C
      (ae_of_all _ (fun x => by
        change ‖((f x / g x : ℝ) : ℂ)‖ ≤ C
        rw [Complex.norm_of_nonneg (div_nonneg (hfp x).le (hgp x).le)]
        exact hC x))
  ((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) (hv.toLp v)

private theorem weightChange_ae (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (C : ℝ) (hC : ∀ x, f x / g x ≤ C) (u : LogL2) :
    (weightChange f g hf hg hfp hgp C hC u : ℝ → ℂ) =ᵐ[volume] fun x => ((f x / g x : ℝ) : ℂ) * u x := by
  let v := fun x : ℝ => ((f x / g x : ℝ) : ℂ)
  have hv : MemLp v ⊤ volume := memLp_top_of_bound
      (Complex.continuous_ofReal.comp (hf.div hg (fun x => (hgp x).ne'))).aestronglyMeasurable C
      (ae_of_all _ (fun x => by
        change ‖((f x / g x : ℝ) : ℂ)‖ ≤ C
        rw [Complex.norm_of_nonneg (div_nonneg (hfp x).le (hgp x).le)]
        exact hC x))
  have hw := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hv.toLp v) u
  refine hw.trans ?_
  filter_upwards [hv.coeFn_toLp] with x hx
  change hv.toLp v x * u x = v x * u x
  rw [hx]

def paperForward (p : ℝ) (hp : 1/2 < p) := weightChange (paperWeight p) (logWeight p)
  (paperWeight_cont p) (continuous_logWeight p) (paperWeight_pos p) (logWeight_pos p) _ (weightRatio_upper (by linarith))
def paperBackward (p : ℝ) (hp : 1/2 < p) := weightChange (logWeight p) (paperWeight p)
  (continuous_logWeight p) (paperWeight_cont p) (logWeight_pos p) (paperWeight_pos p) _ (weightRatio_lower (by linarith))

theorem paperForward_ae (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    (paperForward p hp u : ℝ → ℂ) =ᵐ[volume] fun x => ((paperWeight p x / logWeight p x : ℝ) : ℂ) * u x :=
  weightChange_ae _ _ _ _ _ _ _ _ _
theorem paperBackward_ae (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    (paperBackward p hp u : ℝ → ℂ) =ᵐ[volume] fun x => ((logWeight p x / paperWeight p x : ℝ) : ℂ) * u x :=
  weightChange_ae _ _ _ _ _ _ _ _ _

theorem paper_backward_forward (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    paperBackward p hp (paperForward p hp u) = u := by
  apply Lp.ext
  filter_upwards [paperBackward_ae p hp (paperForward p hp u), paperForward_ae p hp u] with x hx hy
  rw [hx,hy,Complex.ofReal_div,Complex.ofReal_div]
  field_simp [(logWeight_pos p x).ne', (paperWeight_pos p x).ne']

def paperJet (p : ℝ) (hp : 1/2 < p) (i : ZetaJetIndex p) := paperForward p hp (zetaJet p i)
theorem paperJet_ae (p : ℝ) (hp : 1/2 < p) (i : ZetaJetIndex p) :
    (paperJet p hp i : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (paperWeight p x : ℂ) *
      ((x:ℂ)^i.2.val * angularCharacter i.1.val.im x) := by
  filter_upwards [paperForward_ae p hp (zetaJet p i), zetaJet_ae p i] with x hx hi
  change paperForward p hp (zetaJet p i) x = _
  rw [hx,hi,Complex.ofReal_div]
  field_simp [(logWeight_pos p x).ne']

theorem paperJet_independent (p : ℝ) (hp : 1/2 < p) : LinearIndependent ℂ (paperJet p hp) := by
  apply (zetaJet_independent p).map' (paperForward p hp).toLinearMap
  exact LinearMap.ker_eq_bot.mpr (Function.LeftInverse.injective (g := paperBackward p hp) (paper_backward_forward p hp))

def paperShift (p : ℝ) (hp : 1/2 < p) (y : ℝ) : LogL2 →L[ℂ] LogL2 :=
  (paperForward p hp).comp ((weightedTranslation p (by linarith) y).comp (paperBackward p hp))

theorem paperShift_ae (p : ℝ) (hp : 1/2 < p) (y : ℝ) (u : LogL2) :
    (paperShift p hp y u : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      ((paperWeight p x / paperWeight p (x+y) : ℝ) : ℂ) * u (x+y) := by
  have hs := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp (paperBackward_ae p hp u)
  filter_upwards [paperForward_ae p hp (weightedTranslation p (by linarith) y (paperBackward p hp u)),
    weightedTranslation_apply_ae p (by linarith) y (paperBackward p hp u), hs] with x hx ht hb
  change paperForward p hp (weightedTranslation p (by linarith) y (paperBackward p hp u)) x = _
  change paperBackward p hp u (x+y) = _ at hb
  rw [hx,ht,hb]
  change _ * (_ * ((((logWeight p (x+y) / paperWeight p (x+y)) : ℝ) : ℂ) * u (x+y))) = _
  simp only [Complex.ofReal_div]
  field_simp [(logWeight_pos p x).ne',(logWeight_pos p (x+y)).ne',(paperWeight_pos p (x+y)).ne']

theorem paperShift_continuous (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    Continuous (fun y => paperShift p hp y u) :=
  (paperForward p hp).continuous.comp (continuous_weightedTranslation_orbit p (by linarith) (paperBackward p hp u))

theorem paperShift_bound (p : ℝ) (hp : 1/2 < p) (y : ℝ) :
    ‖paperShift p hp y‖ ≤ (‖paperForward p hp‖ * ‖paperBackward p hp‖) * (1+|y|)^⌈p⌉₊ := by
  have hw : ‖weightedTranslation p (by linarith) y‖ ≤ (1+|y|)^⌈p⌉₊ := by
    apply (norm_weightedTranslation_le p (by linarith) y).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (Nat.le_ceil p)
  calc
    _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖paperForward p hp‖ * (‖weightedTranslation p (by linarith) y‖ * ‖paperBackward p hp‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, mul_comm ‖paperBackward p hp‖]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) (norm_nonneg _)

theorem paperShift_triangular (p : ℝ) (hp : 1/2 < p) (ρ : CriticalLineZero)
    (r : Fin (zetaJetCount p ρ)) (y : ℝ) :
    paperShift p hp y (paperJet p hp ⟨ρ,r⟩) = angularCharacter ρ.val.im y •
      ∑ s ∈ Finset.Iic r, ((r.val.choose s.val : ℂ) * (y:ℂ)^(r.val-s.val)) • paperJet p hp ⟨ρ,s⟩ := by
  change paperForward p hp (weightedTranslation p (by linarith) y (paperBackward p hp (paperForward p hp _))) = _
  rw [paper_backward_forward, weightedShift_zetaJet p hp, map_smul, map_sum]
  simp only [map_smul, paperJet]

end
end MasulloRH
end

section
open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH
noncomputable section
def paperJetSpan (p : ℝ) (hp : 1/2 < p) : Submodule ℂ LogL2 := (Submodule.span ℂ (Set.range (paperJet p hp))).topologicalClosure

instance (p : ℝ) (hp : 1/2 < p) : CompleteSpace (paperJetSpan p hp) := inferInstanceAs (CompleteSpace (Submodule.topologicalClosure _))

def paperJetMode (p : ℝ) (hp : 1/2 < p) (j : ZetaJetIndex p) : paperJetSpan p hp :=
  ⟨paperJet p hp j, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j,rfl⟩)⟩

theorem paperJetMode_independent (p : ℝ) (hp : 1/2 < p) : LinearIndependent ℂ (paperJetMode p hp) :=
  LinearIndependent.of_comp (paperJetSpan p hp).subtype (paperJet_independent p hp)

theorem paperJetMode_dense (p : ℝ) (hp : 1/2 < p) :
    Dense (Submodule.span ℂ (Set.range (paperJetMode p hp)) : Set (paperJetSpan p hp)) := by
  rw [Subtype.dense_iff]
  have h : (paperJetSpan p hp).subtype '' (Submodule.span ℂ (Set.range (paperJetMode p hp)) : Set (paperJetSpan p hp)) =
      (Submodule.span ℂ (Set.range (paperJet p hp)) : Set LogL2) := by
    rw [← Submodule.map_coe, Submodule.map_span, ← Set.range_comp]
    rfl
  change (paperJetSpan p hp : Set LogL2) ⊆ closure ((paperJetSpan p hp).subtype '' _)
  rw [h, paperJetSpan, Submodule.topologicalClosure_coe]

private theorem paperJetSpan_invariant (p : ℝ) (hp : 1/2 < p) (y : ℝ) :
    ∀ u ∈ paperJetSpan p hp, paperShift p hp y u ∈ paperJetSpan p hp := by
  unfold paperJetSpan
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rw [Module.End.mem_invtSubmodule_iff_map_le, Submodule.map_span, Submodule.span_le, ← Set.range_comp]
  rintro _ ⟨⟨ρ,r⟩,rfl⟩
  change paperShift p hp y (paperJet p hp ⟨ρ,r⟩) ∈ _
  rw [paperShift_triangular p hp]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  exact fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨ρ,s⟩,rfl⟩)

def paperJetShift (p : ℝ) (hp : 1/2 < p) (y : ℝ) : paperJetSpan p hp →L[ℂ] paperJetSpan p hp :=
  (paperShift p hp y).restrict (paperJetSpan_invariant p hp y)

theorem paperJetShift_continuous (p : ℝ) (hp : 1/2 < p) (u : paperJetSpan p hp) :
    Continuous (fun y => paperJetShift p hp y u) := by
  exact Continuous.subtype_mk (paperShift_continuous p hp u.val) _

theorem paperJetShift_bound (p : ℝ) (hp : 1/2 < p) (y : ℝ) :
    ‖paperJetShift p hp y‖ ≤ (‖paperForward p hp‖ * ‖paperBackward p hp‖) * (1+|y|)^⌈p⌉₊ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖paperShift p hp y (u : LogL2)‖ ≤ _ * ‖(u : LogL2)‖
  exact ((paperShift p hp y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (paperShift_bound p hp y) (norm_nonneg _))

theorem paperJetShift_law (p : ℝ) (hp : 1/2 < p) (ρ : CriticalLineZero)
    (r : Fin (zetaJetCount p ρ)) (y : ℝ) :
    paperJetShift p hp y (paperJetMode p hp ⟨ρ,r⟩) =
      Complex.exp (↑(-2 * Real.pi * y * zetaJetFrequency ρ) * Complex.I) •
      ∑ s ∈ Finset.Iic r, ((r.val.choose s.val : ℂ) * (y:ℂ)^(r.val-s.val)) • paperJetMode p hp ⟨ρ,s⟩ := by
  apply Subtype.ext
  change paperShift p hp y (paperJet p hp ⟨ρ,r⟩) = _
  rw [paperShift_triangular p hp]
  have hf : angularCharacter ρ.val.im y = Complex.exp (↑(-2 * Real.pi * y * zetaJetFrequency ρ) * Complex.I) := by
    rw [angularCharacter, ← Complex.ofReal_mul]
    congr 2
    unfold zetaJetFrequency
    field_simp [Real.pi_ne_zero]
  rw [hf]
  simp only [SetLike.val_smul, Submodule.coe_sum, paperJetMode]

theorem paperJetRange_eq_actual (p : ℝ) (hp : 1/2 < p) :
    Set.range (paperJet p hp) = {u : LogL2 | ∃ (ρ : CriticalLineZero) (r : ℕ),
        r < analyticOrderNatAt riemannZeta ρ.val ∧ (r:ℝ) + 1/2 < p ∧
        (u : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => ((1+x^2)^(-p/2) : ℝ) *
          ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x) * Complex.I))} := by
  ext u
  constructor
  · rintro ⟨⟨ρ,r⟩,rfl⟩
    refine ⟨ρ,r.val,r.isLt.trans_le (min_le_left _ _), zetaJet_admissible (p:=p) ⟨ρ,r⟩, ?_⟩
    simpa only [angularCharacter, paperWeight, Complex.ofReal_mul] using paperJet_ae p hp ⟨ρ,r⟩
  · rintro ⟨ρ,r,hr,hp',hu⟩
    have hcap : r < ⌈p-1/2⌉₊ := Nat.lt_ceil.mpr (by linarith)
    let i : ZetaJetIndex p := ⟨ρ,⟨r,lt_min hr hcap⟩⟩
    refine ⟨i, Lp.ext ((paperJet_ae p hp i).trans ?_)⟩
    simpa only [i,angularCharacter,paperWeight,Complex.ofReal_mul] using hu.symm

theorem paperJetSpan_eq_actual (p : ℝ) (hp : 1/2 < p) :
    paperJetSpan p hp = (Submodule.span ℂ {u : LogL2 | ∃ (ρ : CriticalLineZero) (r : ℕ),
        r < analyticOrderNatAt riemannZeta ρ.val ∧ (r:ℝ) + 1/2 < p ∧
        (u : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => ((1+x^2)^(-p/2) : ℝ) *
          ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x) * Complex.I))}).topologicalClosure := by
  unfold paperJetSpan
  rw [paperJetRange_eq_actual]

end
end MasulloRH
end

section
open MeasureTheory Filter MasulloGRH
open scoped Topology SchwartzMap FourierTransform InnerProductSpace
namespace MasulloRH
noncomputable section

private theorem logTest_integrable_orbit (p : ℝ) (hp : 1/2 < p) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) (u : LogL2) :
    Integrable fun y : ℝ => φ (Real.exp y) • paperShift p hp y u := by
  apply ((hφ.1.continuous.comp Real.continuous_exp).smul (paperShift_continuous p hp u)).integrable_of_hasCompactSupport
  have hk : IsCompact (Real.log '' tsupport φ) := hφ.2.1.image_of_continuousOn
    (Real.continuousOn_log.mono (fun x hx => ne_of_gt (hφ.2.2.1 hx)))
  have hlog : HasCompactSupport (fun y => φ (Real.exp y)) := HasCompactSupport.of_support_subset_isCompact hk (by
    intro y hy
    exact ⟨Real.exp y,subset_tsupport _ hy, Real.log_exp y⟩)
  exact hlog.smul_right

private theorem paper_convolution_pairing (p : ℝ) (hp : 1/2 < p) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) (u g : LogL2) :
    ⟪g, ∫ y : ℝ, φ (Real.exp y) • paperShift p hp y u⟫_ℂ =
      ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
        (((paperWeight p x / paperWeight p (x+y) : ℝ) : ℂ) * u (x+y)) := by
  rw [← integral_inner (logTest_integrable_orbit p hp φ hφ u) g]
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  rw [inner_smul_right, MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [paperShift_ae p hp y u] with x hx
  rw [RCLike.inner_apply', hx]

theorem criticalLine_jet_trace_from_representation
    (p : ℝ) (hp : 1 / 2 < p) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (hrep : ∀ m : 𝓢(ℝ,ℂ), ∃ T : paperJetSpan p hp →L[ℂ] paperJetSpan p hp,
      (∀ u, T u = ∫ y : ℝ, (𝓕⁻ (m : ℝ→ℂ)) y • paperJetShift p hp y u) ∧
      IsNuclearOperator T ∧ HasSum (fun ρ => (zetaJetCount p ρ : ℂ) * m (zetaJetFrequency ρ)) (operatorTrace T)) :
    let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}
    let H := Lp ℂ 2 (volume : Measure ℝ)
    let S := (Submodule.span ℂ {u : H | ∃ (ρ : Z) (r : ℕ), r < analyticOrderNatAt riemannZeta ρ.val ∧
      (r:ℝ)+1/2 < p ∧ (u : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x) * Complex.I))}).topologicalClosure
    ∃! T : S →L[ℂ] S,
      (∀ (u : S) (g : H), ⟪g, (T u : H)⟫_ℂ =
        ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
          ((((1+x^2)^(-p/2) / (1+(x+y)^2)^(-p/2) : ℝ) : ℂ) * (u : H) (x+y))) ∧
      IsNuclearOperator T ∧ HasSum (fun ρ : Z =>
        ((min (analyticOrderNatAt riemannZeta ρ.val) ⌈p-1/2⌉₊ : ℕ) : ℂ) *
          mellin φ (ρ.val - 1/2)) (operatorTrace T) := by
  dsimp only
  rw [← paperJetRange_eq_actual p hp]
  obtain ⟨f,hf⟩ := exists_logTraceTest_schwartz φ hφ
  let m := (𝓕 f : 𝓢(ℝ,ℂ))
  have hF : (𝓕⁻ (⇑m)) = fun y : ℝ => φ (Real.exp y) := by
    rw [← SchwartzMap.fourierInv_coe]
    change (⇑(𝓕⁻ (𝓕 f) : 𝓢(ℝ,ℂ))) = _
    simpa using funext hf
  have hm (ρ : CriticalLineZero) : m (zetaJetFrequency ρ) = mellin φ (ρ.val - 1/2) := by
    have hr : ρ.val - 1/2 = Complex.I * (ρ.val.im : ℂ) := by
      apply Complex.ext <;> simp [ρ.prop.2, Complex.mul_re, Complex.mul_im]
    rw [hr, ← fourier_logTraceTest_eq_mellin]
    change (𝓕 (f : ℝ → ℂ)) (zetaJetFrequency ρ) = _
    rw [funext hf]
    rfl
  obtain ⟨T,hT,hN,htr⟩ := hrep m
  have hop (u : paperJetSpan p hp) : (T u : LogL2) = ∫ y : ℝ, φ (Real.exp y) • paperShift p hp y (u : LogL2) := by
    rw [hT,hF]
    exact ((paperJetSpan p hp).subtypeₗᵢ.integral_comp_comm (fun y : ℝ => φ (Real.exp y) • paperJetShift p hp y u)).symm
  have hpair (u : paperJetSpan p hp) (g : LogL2) := (congrArg (inner ℂ g) (hop u)).trans (paper_convolution_pairing p hp φ hφ (u:LogL2) g)
  refine ⟨T, ⟨hpair, hN, ?_⟩, fun T' ht => ?_⟩
  · simp only [hm, zetaJetCount] at htr
    convert htr using 1
    with_unfolding_all rfl
  · apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    apply ext_inner_left ℂ
    exact fun g => (ht.1 u g).trans (hpair u g).symm

end
end MasulloRH
end

section
open MeasureTheory Filter MasulloRH MasulloGRH
open scoped InnerProductSpace

theorem solution (p : ℝ) (hp : 1 / 2 < p) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}
    let H := Lp ℂ 2 (volume : Measure ℝ)
    let S := (Submodule.span ℂ {u : H | ∃ (ρ : Z) (r : ℕ), r < analyticOrderNatAt riemannZeta ρ.val ∧
      (r:ℝ)+1/2 < p ∧ (u : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x) * Complex.I))}).topologicalClosure
    ∃! T : S →L[ℂ] S,
      (∀ (u : S) (g : H), ⟪g, (T u : H)⟫_ℂ =
        ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
          ((((1+x^2)^(-p/2) / (1+(x+y)^2)^(-p/2) : ℝ) : ℂ) * (u : H) (x+y))) ∧
      IsNuclearOperator T ∧ HasSum (fun ρ : Z =>
        ((min (analyticOrderNatAt riemannZeta ρ.val) ⌈p-1/2⌉₊ : ℕ) : ℂ) *
          mellin φ (ρ.val - 1/2)) (operatorTrace T) := by
  apply criticalLine_jet_trace_from_representation p hp φ hφ
  intro m
  exact MasulloRH.spectral_trace_of_polynomial_translation_jets
    (paperJetShift p hp) ⌈p⌉₊ (‖paperForward p hp‖ * ‖paperBackward p hp‖) (by positivity)
    (paperJetShift_continuous p hp) (paperJetShift_bound p hp)
    (zetaJetCount p) (paperJetMode p hp) zetaJetFrequency
    (paperJetMode_independent p hp) (paperJetMode_dense p hp)
    (paperJetShift_law p hp) (zetaJetCount_summable p) m
end
