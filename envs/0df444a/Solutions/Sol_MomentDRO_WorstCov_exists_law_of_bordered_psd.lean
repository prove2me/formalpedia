-- Prove2me | solution 1 for MomentDRO.WorstCov.exists_law_of_bordered_psd
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T05:16:59.48275+00:00
-- url     : https://prove2.me/submissions/276746bb-f71b-41ab-8ff7-e737a074a50d

import Definitions.Def_MomentDRO_WorstCov_Setting

section
set_option autoImplicit false
open MeasureTheory Matrix
namespace MomentWorstCodex
noncomputable def atomicLaw {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ) :
    Measure (Fin n → ℝ) := ∑ i, ENNReal.ofReal (w i) • Measure.dirac (a i)

lemma atomic_integrable {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (f : (Fin n → ℝ) → ℝ) : Integrable f (atomicLaw a w) := by
  unfold atomicLaw
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma atomic_integral {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : (Fin n → ℝ) → ℝ) :
    (∫ z, f z ∂atomicLaw a w) = ∑ i, w i * f (a i) := by
  unfold atomicLaw
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw i)]
    rfl
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma atomic_probability {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : IsProbabilityMeasure (atomicLaw a w) := by
  constructor
  unfold atomicLaw
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hs]
  simp
lemma atomic_memLp_two {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (f : (Fin n → ℝ) → ℝ) : MemLp f 2 (atomicLaw a w) :=
  (memLp_two_iff_integrable_sq (atomic_integrable a w f).aestronglyMeasurable).mpr
    (atomic_integrable a w (fun z => (f z)^2))

lemma atomic_second_moments {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : MomentDRO.Conf.HasSecondMoments (atomicLaw a w) :=
  ⟨atomic_probability a w hw hs,fun i => atomic_memLp_two a w (fun z => z i)⟩

end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma weights_nonnegative {n K : ℕ} (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) (k : Fin K) : 0 ≤ v k := by
  have h : 0 ≤ bordered (L k) (l k) (v k) (Sum.inr (0 : Fin 1)) (Sum.inr 0) :=
    (hf.2.2 k).diag_nonneg
  simpa [bordered,Matrix.fromBlocks] using h

lemma weights_simplex {n K : ℕ} (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) : v ∈ stdSimplex ℝ (Fin K) :=
  ⟨weights_nonnegative μ Sig γ L l v hf,hf.2.1.2⟩

lemma weights_bounded {n K : ℕ} (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) (k : Fin K) : v k ≤ 1 := by
  have hs := Finset.single_le_sum (fun i _ => weights_nonnegative μ Sig γ L l v hf i) (Finset.mem_univ k)
  rw [hf.2.1.2] at hs
  exact hs

lemma positive_weight_exists {n K : ℕ} (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) : ∃ k, 0 < v k := by
  by_contra hn
  push Not at hn
  have hz (k : Fin K) : v k = 0 := le_antisymm (hn k) (weights_nonnegative μ Sig γ L l v hf k)
  have hs := hf.2.1.2
  simp only [hz,Finset.sum_const_zero] at hs
  norm_num at hs
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
open scoped MatrixOrder
namespace MomentWorstCodex
lemma psd_zero_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (i : ι) (hi : A i i = 0) :
    ∀ j, A j i = 0 := by
  have hq : star (Pi.single i (1 : ℝ)) ⬝ᵥ (A *ᵥ Pi.single i 1) = 0 := by
    simp [dotProduct,mulVec,Pi.single_apply,hi]
  have hz := (hA.dotProduct_mulVec_zero_iff (Pi.single i 1)).mp hq
  intro j
  have hj := congrFun hz j
  simpa [mulVec,dotProduct,Pi.single_apply] using hj

lemma zero_mass_first_moment {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (l : Fin n → ℝ) (h : (bordered L l 0).PosSemidef) : l = 0 := by
  have hz := psd_zero_column (bordered L l 0) h (Sum.inr (0 : Fin 1)) (by simp [bordered,fromBlocks])
  funext i
  have hi := hz (Sum.inl i)
  simpa [bordered,fromBlocks] using hi
lemma psd_entry_squared {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (i j : ι) : (A i j)^2 ≤ A i i * A j j := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB]
  simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial,
    ← sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => B k i) (fun k => B k j)

lemma psd_gram_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) : ∃ B : Matrix ι ι ℝ, A = Bᵀ * B := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B,by simpa [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using hB⟩

end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf
namespace MomentWorstCodex
noncomputable def symAtoms {n : ℕ} (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Fin (n+n) → Fin n → ℝ :=
  Fin.addCases (fun k => μ + Real.sqrt (n : ℝ) • B k) (fun k => μ - Real.sqrt (n : ℝ) • B k)

noncomputable def symLaw {n : ℕ} (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Measure (Fin n → ℝ) := atomicLaw (symAtoms μ B) (fun _ => (2*(n : ℝ))⁻¹)

lemma sym_weights {n : ℕ} (hn : 0 < n) :
    (∀ i : Fin (n+n), 0 ≤ (2*(n : ℝ))⁻¹) ∧
    (∑ _ : Fin (n+n), (2*(n : ℝ))⁻¹) = 1 := by
  constructor
  · intro i; positivity
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add]
    have h : (2*(n : ℝ)) ≠ 0 := by positivity
    rw [show (n : ℝ)+(n : ℝ) = 2*n by ring]
    exact mul_inv_cancel₀ h

lemma sym_second_moments {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    HasSecondMoments (symLaw μ B) :=
  atomic_second_moments _ _ (sym_weights hn).1 (sym_weights hn).2

lemma sym_integral {n : ℕ} (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ z, f z ∂symLaw μ B) = (2*(n : ℝ))⁻¹ *
      ∑ k, (f (μ+Real.sqrt (n : ℝ) • B k) + f (μ-Real.sqrt (n : ℝ) • B k)) := by
  rw [symLaw,atomic_integral _ _ (by intro i; positivity)]
  rw [← Finset.mul_sum,Fin.sum_univ_add]
  simp only [symAtoms,Fin.addCases_left,Fin.addCases_right]
  rw [Finset.sum_add_distrib]

lemma sym_mean {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    meanVec (symLaw μ B) = μ := by
  funext i
  change (∫ z, z i ∂symLaw μ B) = μ i
  rw [sym_integral]
  have hsum : (∑ k : Fin n, ((μ+Real.sqrt (n : ℝ) • B k) i + (μ-Real.sqrt (n : ℝ) • B k) i)) =
      (n : ℝ)*(2*μ i) := by
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    simp_rw [show ∀ k : Fin n, μ i+Real.sqrt (n : ℝ)*B k i+(μ i-Real.sqrt (n : ℝ)*B k i) = 2*μ i by intro k; ring]
    simp
  rw [hsum]
  have h : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma sym_second {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    secondMomentAbout (symLaw μ B) 0 = Matrix.vecMulVec μ μ + Bᵀ*B := by
  ext i j
  change (∫ z, (z i-0)*(z j-0) ∂symLaw μ B) = _
  simp only [sub_zero]
  rw [sym_integral]
  have he (k : Fin n) :
      (μ+Real.sqrt (n : ℝ) • B k) i*(μ+Real.sqrt (n : ℝ) • B k) j +
      (μ-Real.sqrt (n : ℝ) • B k) i*(μ-Real.sqrt (n : ℝ) • B k) j =
        2*μ i*μ j + 2*(n : ℝ)*(B k i*B k j) := by
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    calc
      _ = 2*μ i*μ j + 2*(Real.sqrt (n : ℝ))^2*(B k i*B k j) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [Matrix.add_apply,Matrix.vecMulVec_apply,Matrix.mul_apply,Matrix.transpose_apply]
  have h : (n : ℝ) ≠ 0 := by positivity
  field_simp
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma bordered_quadratic {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (l q : Fin n → ℝ) (v t : ℝ) :
    (Sum.elim q (fun _ : Fin 1 => t)) ⬝ᵥ
      (bordered L l v *ᵥ Sum.elim q (fun _ : Fin 1 => t)) =
        q ⬝ᵥ (L *ᵥ q) + 2*t*(q ⬝ᵥ l) + v*t^2 := by
  simp [bordered,dotProduct,mulVec,Fintype.sum_sum_type,Fin.sum_univ_one,Matrix.fromBlocks,
    mul_add,add_mul,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  change (∑ i, q i*(∑ j, L i j*q j))+t*(∑ i,l i*q i)+
    ((∑ i,q i*(l i*t))+t*(v*t)) =
      (∑ i,q i*(∑ j,L i j*q j))+2*t*(∑ i,q i*l i)+v*t^2
  have hc : (∑ k, l k*q k) = ∑ k, q k*l k := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have ht : (∑ k, q k*(l k*t)) = t*∑ k, q k*l k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hc,ht]
  ring

lemma scaled_covariance_psd {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (l : Fin n → ℝ) (v : ℝ) (hv : 0 < v) (h : (bordered L l v).PosSemidef) :
    (v⁻¹ • L - Matrix.vecMulVec (v⁻¹ • l) (v⁻¹ • l)).PosSemidef := by
  have htop : (bordered L l v).submatrix Sum.inl Sum.inl = L := by
    ext i j
    simp [bordered,Matrix.submatrix,Matrix.fromBlocks]
  have hL : L.PosSemidef := by
    rw [← htop]
    exact h.submatrix Sum.inl
  have hμ : (Matrix.vecMulVec (v⁻¹ • l) (v⁻¹ • l)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v⁻¹ • l)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hL.smul (inv_nonneg.mpr hv.le)).1.sub hμ.1)
  intro q
  let d := q ⬝ᵥ l
  have hp := h.dotProduct_mulVec_nonneg (Sum.elim q (fun _ : Fin 1 => -(v⁻¹*d)))
  simp only [star_trivial] at hp
  rw [bordered_quadratic] at hp
  change 0 ≤ q ⬝ᵥ (L *ᵥ q)+2*(-(v⁻¹*d))*d+v*(-(v⁻¹*d))^2 at hp
  have he : q ⬝ᵥ (L *ᵥ q)+2*(-(v⁻¹*d))*d+v*(-(v⁻¹*d))^2 =
      q ⬝ᵥ (L *ᵥ q)-v⁻¹*d^2 := by field_simp [hv.ne']; ring
  rw [he] at hp
  have hdot : q ⬝ᵥ (v⁻¹ • l) = v⁻¹*d := by simp [d,dotProduct_smul,smul_eq_mul]
  have hc : q ⬝ᵥ ((v⁻¹ • L - Matrix.vecMulVec (v⁻¹ • l) (v⁻¹ • l)) *ᵥ q) =
      v⁻¹*(q ⬝ᵥ (L *ᵥ q)-v⁻¹*d^2) := by
    rw [sub_mulVec,smul_mulVec,dotProduct_sub,dotProduct_smul,vecMulVec_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul,op_smul_eq_mul]
    rw [dotProduct_comm (v⁻¹ • l) q,hdot]
    ring
  simp only [star_trivial]
  rw [hc]
  exact mul_nonneg (inv_nonneg.mpr hv.le) hp

end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma exists_law_mean_cov {n : ℕ} (μ : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) :
    ∃ P : Measure (Fin n → ℝ), HasSecondMoments P ∧ meanVec P = μ ∧
      secondMomentAbout P 0 = C + Matrix.vecMulVec μ μ := by
  obtain ⟨B,hB⟩ := psd_gram_factor C hC
  by_cases hn : n = 0
  · subst n
    refine ⟨Measure.dirac μ,⟨inferInstance,fun i => Fin.elim0 i⟩,?_,?_⟩
    · funext i; exact Fin.elim0 i
    · ext i j; exact Fin.elim0 i
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    refine ⟨symLaw μ B,sym_second_moments hpos μ B,sym_mean hpos μ B,?_⟩
    rw [sym_second hpos μ B,← hB,add_comm]

theorem exists_law_of_bordered_psd {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ)
    (v : ℝ) (hv : 0 < v) (hpsd : (bordered L l v).PosSemidef) :
    ∃ P : Measure (Fin n → ℝ), HasSecondMoments P ∧
      meanVec P = v⁻¹ • l ∧ secondMomentAbout P 0 = v⁻¹ • L := by
  let μ := v⁻¹ • l
  let C := v⁻¹ • L - Matrix.vecMulVec μ μ
  have hc : C.PosSemidef := scaled_covariance_psd L l v hv hpsd
  obtain ⟨P,hP,hmean,hraw⟩ := exists_law_mean_cov μ C hc
  refine ⟨P,hP,hmean,?_⟩
  rw [hraw]
  dsimp [C]
  abel
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.WorstCov
theorem solution {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ)
    (v : ℝ) (hv : 0 < v) (hpsd : (bordered L l v).PosSemidef) :
    ∃ P : Measure (Fin n → ℝ), MomentDRO.Conf.HasSecondMoments P ∧
      MomentDRO.Conf.meanVec P = v⁻¹ • l ∧ MomentDRO.Conf.secondMomentAbout P 0 = v⁻¹ • L := MomentWorstCodex.exists_law_of_bordered_psd L l v hv hpsd

end

#print axioms solution
