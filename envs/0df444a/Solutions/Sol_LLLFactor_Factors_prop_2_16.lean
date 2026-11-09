-- Prove2me | solution 1 for LLLFactor.Factors.prop_2_16
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T21:59:41.249913+00:00
-- url     : https://prove2.me/submissions/5e64f2bb-bd96-4773-9265-dd71cf8f6347

import Definitions.Def_LLLFactor_Factors_Setting
import Theorems.Thm_LLLFactor_Factors_prop_2_5
import Theorems.Thm_LLLFactor_Factors_prop_2_7
import Theorems.Thm_LLLFactor_Factors_prop_2_13
import Theorems.Thm_LLLFactor_Factors_card_le_2_18
import Theorems.Thm_LLLFactor_Factors_subset_2_19

open Polynomial Finset Submodule LLLFactor.Factors

namespace Prop216Proof
noncomputable section

lemma polyNorm_nonneg (f : ℤ[X]) : 0 ≤ polyNorm f := Real.sqrt_nonneg _

lemma polyNorm_sq (f : ℤ[X]) :
    polyNorm f ^ 2 = ∑ i ∈ f.support, (f.coeff i : ℝ) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma sum_coeff_sq_le (f : ℤ[X]) (s : Finset ℕ) :
    (∑ i ∈ s, (f.coeff i : ℝ) ^ 2) ≤ polyNorm f ^ 2 := by
  rw [polyNorm_sq]
  calc
    _ ≤ ∑ i ∈ f.support ∪ s, (f.coeff i : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (by intros; positivity)
    _ = _ := (Finset.sum_subset Finset.subset_union_left (by
      intro i _ hi
      simp [Polynomial.notMem_support_iff.mp hi])).symm

lemma one_le_polyNorm {f : ℤ[X]} (hf : f ≠ 0) : 1 ≤ polyNorm f := by
  have hc : (1 : ℝ) ≤ |(f.leadingCoeff : ℝ)| := by
    exact_mod_cast (Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hf))
  have hs := sum_coeff_sq_le f {f.natDegree}
  simp only [Finset.sum_singleton, coeff_natDegree] at hs
  have hn := polyNorm_nonneg f
  nlinarith [sq_abs (f.leadingCoeff : ℝ)]

lemma polyNorm_pos {f : ℤ[X]} (hf : f ≠ 0) : 0 < polyNorm f :=
  lt_of_lt_of_le zero_lt_one (one_le_polyNorm hf)

lemma coeffVec_zero (m : ℕ) : coeffVec m 0 = 0 := by
  ext i
  simp [coeffVec]

lemma coeffVec_sum_zsmul {ι : Type*} [Fintype ι] (m : ℕ) (b : ι → ℤ[X]) (z : ι → ℤ) :
    coeffVec m (∑ i, z i • b i) = ∑ i, (z i : ℝ) • coeffVec m (b i) := by
  ext j
  simp [coeffVec, zsmul_eq_mul]

lemma coeffVec_integer_expansion {ι : Type*} [Fintype ι] (m : ℕ) (b : ι → ℤ[X])
    (f : ℤ[X]) (hf : f ∈ Submodule.span ℤ (Set.range b)) :
    ∃ z : ι → ℤ, ∑ i, (z i : ℝ) • coeffVec m (b i) = coeffVec m f := by
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hf
  refine ⟨z, ?_⟩
  rw [← coeffVec_sum_zsmul, hz]

lemma basis_polynomial_ne_zero {p k m : ℕ} {h : ℤ[X]} {b : Fin (m + 1) → ℤ[X]}
    (hb : IsReducedBasisOfL p k h m b) (j : Fin (m + 1)) : b j ≠ 0 := by
  intro hz
  have hn := hb.2.1.ne_zero j
  apply hn
  change coeffVec m (b j) = 0
  rw [hz, coeffVec_zero]

lemma threshold_pow (F P : ℝ) (m n : ℕ) (hF : 0 < F) (hP : 0 < P) (hn : 0 < n) :
    ((P / F ^ m) ^ ((1 : ℝ) / (n : ℝ))) ^ n = P / F ^ m := by
  rw [← Real.rpow_mul_natCast (le_of_lt (div_pos hP (pow_pos hF _)))]
  rw [div_mul_cancel₀ (1 : ℝ) (by exact_mod_cast ne_of_gt hn), Real.rpow_one]

lemma threshold_iff (F P B : ℝ) (m n : ℕ) (hF : 0 < F) (hP : 0 < P)
    (hB : 0 ≤ B) (hn : 0 < n) :
    B < (P / F ^ m) ^ ((1 : ℝ) / (n : ℝ)) ↔ F ^ m * B ^ n < P := by
  have hp := threshold_pow F P m n hF hP hn
  have ht : 0 ≤ (P / F ^ m) ^ ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_nonneg (le_of_lt (div_pos hP (pow_pos hF _))) _
  have he := Real.rpow_lt_rpow_iff hB ht (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
  rw [Real.rpow_natCast, Real.rpow_natCast, hp] at he
  rw [← he, lt_div_iff₀ (pow_pos hF _)]
  exact ⟨fun h => by simpa only [mul_comm] using h, fun h => by simpa only [mul_comm] using h⟩

lemma shifts_independent {m d : ℕ} (h : ℤ[X]) (hh : h ≠ 0)
    (hd : h.natDegree + d ≤ m + 1) :
    LinearIndependent ℝ (fun i : Fin d => coeffVec m (X ^ i.val * h)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  by_contra hi
  let s := Finset.univ.filter (fun j => a j ≠ 0)
  have hs : s.Nonempty := ⟨i, by simp [s, hi]⟩
  let r := s.max' hs
  have hr : a r ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have ht : ∀ j, r < j → a j = 0 := by
    intro j hj
    by_contra hz
    exact (not_le_of_gt hj) (Finset.le_max' s j (by simp [s, hz]))
  have hb : h.natDegree + r.val < m + 1 := by have := r.isLt; omega
  have he := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v ⟨h.natDegree + r.val, hb⟩) ha
  have he' : (∑ j : Fin d, a j * ((X ^ j.val * h).coeff (h.natDegree + r.val) : ℝ)) = 0 := by
    simpa [coeffVec] using he
  rw [Finset.sum_eq_single r] at he'
  · rw [Polynomial.coeff_X_pow_mul, Polynomial.coeff_natDegree] at he'
    have hl : (h.leadingCoeff : ℝ) ≠ 0 := by exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hh
    exact hr (mul_eq_zero.mp he' |>.resolve_right hl)
  · intro j _ hjr
    rcases lt_or_gt_of_ne hjr with hj | hj
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · simp
      · rw [Polynomial.natDegree_X_pow_mul j.val hh]
        have : j.val < r.val := hj
        omega
    · simp [ht j hj]
  · simp

lemma multiple_integer_span {m : ℕ} {h f : ℤ[X]} (hh : h ≠ 0)
    (hhm : h.natDegree ≤ m) (hf : f.natDegree ≤ m) (hdiv : h ∣ f) :
    f ∈ Submodule.span ℤ (Set.range (fun i : Fin (m - h.natDegree + 1) => X ^ i.val * h)) := by
  classical
  by_cases hz : f = 0
  · simp [hz]
  obtain ⟨q, rfl⟩ := hdiv
  have hq : q ≠ 0 := by intro h; simp [h] at hz
  have hd : q.natDegree < m - h.natDegree + 1 := by
    rw [Polynomial.natDegree_mul hh hq] at hf
    omega
  have he : h * q = ∑ i : Fin (m - h.natDegree + 1), q.coeff i • (X ^ i.val * h) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => q.coeff i • (X ^ i * h)) (m - h.natDegree + 1)]
    conv_lhs => rw [q.as_sum_range_C_mul_X_pow' hd]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Polynomial.smul_eq_C_mul, mul_comm, mul_assoc]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma multiple_coeff_span {m : ℕ} {h f : ℤ[X]} (hh : h ≠ 0)
    (hhm : h.natDegree ≤ m) (hf : f.natDegree ≤ m) (hdiv : h ∣ f) :
    coeffVec m f ∈ Submodule.span ℝ
      (Set.range (fun i : Fin (m - h.natDegree + 1) => coeffVec m (X ^ i.val * h))) := by
  obtain ⟨z, hz⟩ := coeffVec_integer_expansion m _ f (multiple_integer_span hh hhm hf hdiv)
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨fun i => (z i : ℝ), hz⟩

lemma prefix_range_eq {N d : ℕ} (hd : d ≤ N) (v : Fin N → EuclideanSpace ℝ (Fin N)) :
    Set.range (fun i : Fin d => v ⟨i.val, lt_of_lt_of_le i.isLt hd⟩) =
      v '' {i : Fin N | i.val < d} := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hd⟩, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩

lemma independent_not_prefix {N d : ℕ} (hd : d ≤ N)
    {v : Fin N → EuclideanSpace ℝ (Fin N)} (hv : LinearIndependent ℝ v)
    (r : Fin N) (hr : d ≤ r.val) :
    v r ∉ Submodule.span ℝ (Set.range (fun i : Fin d => v ⟨i.val, lt_of_lt_of_le i.isLt hd⟩)) := by
  rw [prefix_range_eq hd v]
  exact hv.notMem_span_image (by simp only [Set.mem_ofPred_eq]; omega)

lemma prefix_span_eq {N d : ℕ} (hd : d ≤ N)
    (v : Fin N → EuclideanSpace ℝ (Fin N)) (hv : LinearIndependent ℝ v)
    (x : Fin d → EuclideanSpace ℝ (Fin N)) (hx : LinearIndependent ℝ x)
    (hmem : ∀ i : Fin d, v ⟨i.val, lt_of_lt_of_le i.isLt hd⟩ ∈ Submodule.span ℝ (Set.range x)) :
    Submodule.span ℝ (Set.range (fun i : Fin d => v ⟨i.val, lt_of_lt_of_le i.isLt hd⟩)) =
      Submodule.span ℝ (Set.range x) := by
  have hp : LinearIndependent ℝ (fun i : Fin d => v ⟨i.val, lt_of_lt_of_le i.isLt hd⟩) :=
    hv.comp _ (by intro i j h; exact Fin.ext (congrArg (fun z : Fin N => z.val) h))
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact hmem i
  · rw [finrank_span_eq_card hp, finrank_span_eq_card hx]

lemma sum_prefix_extend {N d : ℕ} (hd : d ≤ N)
    (v : Fin N → EuclideanSpace ℝ (Fin N)) (a : Fin d → ℝ) :
    (∑ j : Fin N, (if hj : j.val < d then a ⟨j.val, hj⟩ else 0) • v j) =
      ∑ i : Fin d, a i • v ⟨i.val, lt_of_lt_of_le i.isLt hd⟩ := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => j.val < d)
  calc
    _ = ∑ j ∈ s, (if hj : j.val < d then a ⟨j.val, hj⟩ else 0) • v j := by
      apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro j _ hj
      have h : ¬ j.val < d := by simpa [s] using hj
      simp [h]
    _ = _ := by
      apply Finset.sum_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin d))
      · intro j hj; exact Finset.mem_univ _
      · intro j hj k hk he
        exact Fin.ext (congrArg (fun z : Fin d => z.val) he)
      · intro i _
        refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hd⟩, ?_, rfl⟩
        simp [s]
      · intro j hj
        simp only [dif_pos (Finset.mem_filter.mp hj).2]

lemma common_divisor_of_prefix_span {m d : ℕ} (hd : d ≤ m + 1)
    (b : Fin (m + 1) → ℤ[X]) (hb : LinearIndependent ℝ (coeffVec m ∘ b))
    (f : ℤ[X]) (hf : f ∈ Submodule.span ℤ (Set.range b))
    (hspan : coeffVec m f ∈ Submodule.span ℝ
      (Set.range (fun i : Fin d => coeffVec m (b ⟨i.val, lt_of_lt_of_le i.isLt hd⟩))))
    (g : ℤ[X]) (hg : ∀ i : Fin (m + 1), i.val < d → g ∣ b i) : g ∣ f := by
  classical
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hf
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  have he : (∑ i, (z i : ℝ) • (coeffVec m ∘ b) i) =
      ∑ i, (if hi : i.val < d then a ⟨i.val, hi⟩ else 0) • (coeffVec m ∘ b) i := by
    rw [sum_prefix_extend hd]
    change (∑ i, (z i : ℝ) • coeffVec m (b i)) = _
    rw [← coeffVec_sum_zsmul, hz]
    exact ha.symm
  have htail : ∀ i : Fin (m + 1), d ≤ i.val → z i = 0 := by
    intro i hi
    have hc := hb.eq_coords_of_eq he i
    rw [dif_neg (by omega)] at hc
    exact_mod_cast hc
  rw [← hz]
  apply Finset.dvd_sum
  intro i _
  by_cases hi : i.val < d
  · rw [Polynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right (hg i hi) _
  · simp [htail i (by omega)]

end
end Prop216Proof

theorem solution {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (hm : h.natDegree ≤ m) (h₀ : ℤ[X]) (hh₀ : IsH0 p f h h₀)
    (b : Fin (m + 1) → ℤ[X]) (hb : IsReducedBasisOfL p k h m b)
    (h214 : (2 : ℝ) ^ ((m : ℝ) * (f.natDegree : ℝ) / 2) *
        ((Nat.choose (2 * m) m : ℕ) : ℝ) ^ ((f.natDegree : ℝ) / 2) *
        polyNorm f ^ (m + f.natDegree) < (p : ℝ) ^ (k * h.natDegree))
    (t : ℕ) (ht1 : 1 ≤ t) (htm : t ≤ m + 1)
    (htJ : polyNorm (b ⟨t - 1, by omega⟩) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ)))
    (htmax : ∀ j : Fin (m + 1), t ≤ (j : ℕ) →
      ¬ polyNorm (b j) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ))) :
    h₀.natDegree = m + 1 - t ∧
    ((∀ j : Fin (m + 1), (j : ℕ) < t → h₀ ∣ b j) ∧
      (∀ g : ℤ[X], (∀ j : Fin (m + 1), (j : ℕ) < t → g ∣ b j) → g ∣ h₀)) ∧
    (∀ j : Fin (m + 1), (j : ℕ) < t →
      polyNorm (b j) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ))) := by
  have hf : f ≠ 0 := by
    intro hz
    have hn := hS.deg_f_pos
    simp [hz] at hn
  have hp : (0 : ℝ) < p := by exact_mod_cast hS.prime.pos
  have hP : (0 : ℝ) < (p : ℝ) ^ (k * h.natDegree) := pow_pos hp _
  have hF := Prop216Proof.polyNorm_pos hf
  have hlast : h₀ ∣ b ⟨t - 1, by omega⟩ :=
    (prop_2_7 f h hS m hm h₀ hh₀ (b ⟨t - 1, by omega⟩) (hb.1 _)
      ((Prop216Proof.threshold_iff (polyNorm f) ((p : ℝ) ^ (k * h.natDegree))
        (polyNorm (b ⟨t - 1, by omega⟩)) m f.natDegree hF hP
        (Prop216Proof.polyNorm_nonneg _) hS.deg_f_pos).mp htJ)).1
  have hd0 : h₀.natDegree ≤ m :=
    (Polynomial.natDegree_le_of_dvd hlast
      (Prop216Proof.basis_polynomial_ne_zero hb _)).trans (hb.1 _).1
  let d := m - h₀.natDegree + 1
  have hdN : d ≤ m + 1 := by dsimp [d]; omega
  have hshort : ∀ j : Fin (m + 1), j.val < d →
      polyNorm (b j) < ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ)) := by
    intro j hj
    exact subset_2_19 f h hS m hm h₀ hh₀ b hb h214 hd0 j (by dsimp [d] at hj; omega)
  have hdiv : ∀ j : Fin (m + 1), j.val < d → h₀ ∣ b j := by
    intro j hj
    exact (prop_2_7 f h hS m hm h₀ hh₀ (b j) (hb.1 j)
      ((Prop216Proof.threshold_iff (polyNorm f) ((p : ℝ) ^ (k * h.natDegree))
        (polyNorm (b j)) m f.natDegree hF hP
        (Prop216Proof.polyNorm_nonneg _) hS.deg_f_pos).mp (hshort j hj))).1
  let x : Fin d → EuclideanSpace ℝ (Fin (m + 1)) := fun i => coeffVec m (X ^ i.val * h₀)
  have hx : LinearIndependent ℝ x :=
    Prop216Proof.shifts_independent h₀ hh₀.1.ne_zero (by dsimp [d]; omega)
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin d =>
      coeffVec m (b ⟨i.val, lt_of_lt_of_le i.isLt hdN⟩))) = Submodule.span ℝ (Set.range x) := by
    apply Prop216Proof.prefix_span_eq hdN (coeffVec m ∘ b) hb.2.1 x hx
    intro i
    exact Prop216Proof.multiple_coeff_span hh₀.1.ne_zero hd0 (hb.1 _).1 (hdiv _ i.isLt)
  have htd : t ≤ d := by
    by_contra ht
    have hmem := Prop216Proof.multiple_coeff_span hh₀.1.ne_zero hd0 (hb.1 ⟨t - 1, by omega⟩).1 hlast
    have hnot := Prop216Proof.independent_not_prefix hdN hb.2.1 ⟨t - 1, by omega⟩
      (by change d ≤ t - 1; omega)
    apply hnot
    change coeffVec m (b ⟨t - 1, by omega⟩) ∈ Submodule.span ℝ
      (Set.range (fun i : Fin d => coeffVec m (b ⟨i.val, lt_of_lt_of_le i.isLt hdN⟩)))
    rw [hspan]
    exact hmem
  have hdt : d ≤ t := by
    by_contra ht
    have htN : t < m + 1 := by omega
    exact htmax ⟨t, htN⟩ (by simp) (hshort ⟨t, htN⟩ (by change t < d; omega))
  have hteq : t = d := le_antisymm htd hdt
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · dsimp [d] at hteq
    omega
  · intro j hj
    exact hdiv j (by omega)
  · intro g hg
    apply Prop216Proof.common_divisor_of_prefix_span hdN b hb.2.1 h₀
      (hb.2.2.1 h₀ ⟨hd0, (prop_2_5 f h hS).2.2.2 h₀ hh₀⟩)
    · rw [hspan]
      exact Prop216Proof.multiple_coeff_span hh₀.1.ne_zero hd0 hd0 (dvd_refl _)
    · intro j hj
      exact hg j (by omega)
  · intro j hj
    exact hshort j (by omega)
