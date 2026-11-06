-- Prove2me | solution 1 for MinimaxSLP.RhsExtremal.mixture_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:04:42.826042+00:00
-- url     : https://prove2.me/submissions/92edb65c-b136-4d27-b97b-823328cd9147

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model
import Theorems.Thm_MinimaxSLP_RhsExtremal_disutility_Qval_eq_max_pairs

open Matrix MinimaxSLP.ObjSDP

namespace RhsExtH

variable {r : ℕ}

@[simp] lemma bord_ll (V : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) (v0 : ℝ) (a b : Fin r) :
    bordered V v v0 (Sum.inl a) (Sum.inl b) = V a b := by simp [bordered]
@[simp] lemma bord_lr (V : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) (v0 : ℝ) (a : Fin r) (b : Fin 1) :
    bordered V v v0 (Sum.inl a) (Sum.inr b) = v a := by simp [bordered]
@[simp] lemma bord_rl (V : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) (v0 : ℝ) (a : Fin 1) (b : Fin r) :
    bordered V v v0 (Sum.inr a) (Sum.inl b) = v b := by simp [bordered]
@[simp] lemma bord_rr (V : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) (v0 : ℝ) (a b : Fin 1) :
    bordered V v v0 (Sum.inr a) (Sum.inr b) = v0 := by simp [bordered]

lemma bord_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :
    ∑ x ∈ s, bordered (f x).1 (f x).2.1 (f x).2.2 =
      bordered (∑ x ∈ s, (f x).1) (∑ x ∈ s, (f x).2.1) (∑ x ∈ s, (f x).2.2) := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.sum_apply, Finset.sum_apply]

lemma bord_inj {V V' : Matrix (Fin r) (Fin r) ℝ} {v v' : Fin r → ℝ} {a a' : ℝ}
    (h : bordered V v a = bordered V' v' a') : V = V' ∧ v = v' ∧ a = a' := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; simpa using congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  · ext i; simpa using congrFun (congrFun h (Sum.inl i)) (Sum.inr 0)
  · simpa using congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)

lemma bord_quad (V : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) (v0 : ℝ)
    (x : Fin r ⊕ Fin 1 → ℝ) :
    x ⬝ᵥ (bordered V v v0 *ᵥ x) = (x ∘ Sum.inl) ⬝ᵥ (V *ᵥ (x ∘ Sum.inl)) +
      2 * x (Sum.inr 0) * (v ⬝ᵥ (x ∘ Sum.inl)) + x (Sum.inr 0) ^ 2 * v0 := by
  have hx : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by ext i; rcases i <;> rfl
  have h1 : (Matrix.of fun i (_ : Fin 1) => v i) *ᵥ (x ∘ Sum.inr) = x (Sum.inr 0) • v := by
    ext i; simp [mulVec, dotProduct, mul_comm]
  have h2 : (Matrix.of fun (_ : Fin 1) j => v j) *ᵥ (x ∘ Sum.inl) = fun _ => v ⬝ᵥ (x ∘ Sum.inl) := by
    ext i; simp [mulVec, dotProduct]
  have h3 : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v0) *ᵥ (x ∘ Sum.inr) = fun _ => v0 * x (Sum.inr 0) := by
    ext i; simp [mulVec, dotProduct]
  conv_lhs => rw [hx]
  rw [bordered, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, h1, h2, h3]
  have h4 : ∀ f : Fin 1 → ℝ, (x ∘ Sum.inr) ⬝ᵥ f = x (Sum.inr 0) * f 0 := by
    intro f; simp [dotProduct]
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm (x ∘ Sum.inl) v, h4]
  simp only [Pi.add_apply]
  ring

lemma bord_transpose (V : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) (v0 : ℝ) :
    (bordered V v v0)ᵀ = bordered Vᵀ v v0 := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> simp

lemma bord_psd_of {V : Matrix (Fin r) (Fin r) ℝ} {v : Fin r → ℝ} {v0 : ℝ} (hV : V.IsSymm)
    (h : ∀ (a : Fin r → ℝ) (t : ℝ), 0 ≤ a ⬝ᵥ (V *ᵥ a) + 2 * t * (v ⬝ᵥ a) + t ^ 2 * v0) :
    (bordered V v v0).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · show (bordered V v v0)ᴴ = bordered V v v0
    rw [conjTranspose_eq_transpose_of_trivial, bord_transpose, hV.eq]
  · rw [star_trivial, bord_quad]; exact h _ _

lemma bord_quad_nonneg {V : Matrix (Fin r) (Fin r) ℝ} {v : Fin r → ℝ} {v0 : ℝ}
    (hP : (bordered V v v0).PosSemidef) (a : Fin r → ℝ) (t : ℝ) :
    0 ≤ a ⬝ᵥ (V *ᵥ a) + 2 * t * (v ⬝ᵥ a) + t ^ 2 * v0 := by
  have := hP.dotProduct_mulVec_nonneg (Sum.elim a (fun _ => t))
  rw [star_trivial, bord_quad] at this
  simpa [Function.comp_def] using this

lemma bord_symm {V : Matrix (Fin r) (Fin r) ℝ} {v : Fin r → ℝ} {v0 : ℝ}
    (hP : (bordered V v v0).PosSemidef) : V.IsSymm := by
  have h := hP.1
  have : (bordered V v v0)ᵀ = bordered V v v0 := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact h
  rw [bord_transpose] at this
  exact (bord_inj this).1

lemma bord_V_psd {V : Matrix (Fin r) (Fin r) ℝ} {v : Fin r → ℝ} {v0 : ℝ}
    (hP : (bordered V v v0).PosSemidef) : V.PosSemidef := by
  have := hP.submatrix Sum.inl
  have e : (bordered V v v0).submatrix Sum.inl Sum.inl = V := by ext i j; simp
  rwa [e] at this

lemma bord_v0_nonneg {V : Matrix (Fin r) (Fin r) ℝ} {v : Fin r → ℝ} {v0 : ℝ}
    (hP : (bordered V v v0).PosSemidef) : 0 ≤ v0 := by
  have := hP.diag_nonneg (i := Sum.inr 0); simpa using this

lemma bord_v_zero {V : Matrix (Fin r) (Fin r) ℝ} {v : Fin r → ℝ}
    (hP : (bordered V v 0).PosSemidef) : v = 0 := by
  have hq := bord_quad_nonneg hP v
  by_contra hne
  have hw : 0 < v ⬝ᵥ v := by
    rcases lt_or_eq_of_le (dotProduct_self_star_nonneg v) with h | h
    · simpa using h
    · exact absurd (dotProduct_self_eq_zero.mp (by simpa using h.symm)) hne
  set c0 := v ⬝ᵥ (V *ᵥ v)
  have := hq (-(c0 + 1) / (2 * (v ⬝ᵥ v)))
  have e : 2 * (-(c0 + 1) / (2 * (v ⬝ᵥ v))) * (v ⬝ᵥ v) = -(c0 + 1) := by
    field_simp
  nlinarith

lemma psd_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (i j : ι) : |B i j| ≤ (B i i + B j j) / 2 := by
  by_cases hij : i = j
  · subst hij
    have := hB.diag_nonneg (i := i)
    rw [abs_of_nonneg this]; linarith
  have hs : B j i = B i j := by
    have := hB.1.apply i j; simpa using this
  have hq : ∀ c : ℝ, 0 ≤ B i i + 2 * c * B i j + c ^ 2 * B j j := by
    intro c
    have := hB.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j c)
    rw [star_trivial] at this
    simp only [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single, dotProduct_single,
      single_dotProduct, Pi.single_apply, if_neg hij, if_neg (Ne.symm hij)] at this
    simp [mulVec, dotProduct, Pi.single_apply, hij, Ne.symm hij] at this
    rw [hs] at this; nlinarith
  rw [abs_le]
  constructor
  · have := hq 1; nlinarith
  · have := hq (-1); nlinarith

open MinimaxSLP.RhsExtremal in
lemma bord_sum2 {K N : ℕ} (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)) :
    ∑ k, ∑ i, bordered (s k i).1 (s k i).2.1 (s k i).2.2 =
      bordered (∑ k, ∑ i, (s k i).1) (∑ k, ∑ i, (s k i).2.1) (∑ k, ∑ i, (s k i).2.2) := by
  ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.sum_apply, Finset.sum_apply]

open MinimaxSLP.RhsExtremal in
lemma feas_iff {K N : ℕ} (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)) :
    s ∈ feasible16 K N μ Q ↔ (∑ k, ∑ i, (s k i).1 = Q ∧ ∑ k, ∑ i, (s k i).2.1 = μ ∧
      ∑ k, ∑ i, (s k i).2.2 = 1) ∧ ∀ k i, (bordered (s k i).1 (s k i).2.1 (s k i).2.2).PosSemidef := by
  unfold feasible16
  simp only [Set.mem_setOf_eq, bord_sum2]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨bord_inj h1, h2⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨by rw [h1, h2, h3], h4⟩

lemma bord_zero : bordered (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 = 0 := by
  ext a b; rcases a with a | a <;> rcases b with b | b <;> simp

lemma bord_add (V V' : Matrix (Fin r) (Fin r) ℝ) (v v' : Fin r → ℝ) (a a' : ℝ) :
    bordered (V + V') (v + v') (a + a') = bordered V v a + bordered V' v' a' := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> simp

lemma isClosed_psd {ι : Type*} [Fintype ι] : IsClosed {M : Matrix ι ι ℝ | M.PosSemidef} := by
  have : {M : Matrix ι ι ℝ | M.PosSemidef} =
      {M | Mᴴ = M} ∩ ⋂ x : ι → ℝ, {M | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      posSemidef_iff_dotProduct_mulVec]; rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

end RhsExtH


open MeasureTheory ProbabilityTheory Matrix MinimaxSLP.RhsExtremal

namespace RhsExtG

variable {r : ℕ}

lemma memLp_coord (m : EuclideanSpace ℝ (Fin r)) (S : Matrix (Fin r) (Fin r) ℝ) (a : Fin r) :
    MemLp (fun z : EuclideanSpace ℝ (Fin r) => z a) 2 (multivariateGaussian m S) := by
  have := IsGaussian.memLp_dual (multivariateGaussian m S) (EuclideanSpace.proj a) 2 (by simp)
  simpa using this

lemma integral_coord (m : EuclideanSpace ℝ (Fin r)) (S : Matrix (Fin r) (Fin r) ℝ) (a : Fin r) :
    ∫ z, z a ∂(multivariateGaussian m S) = m a := by
  have := (EuclideanSpace.proj (𝕜 := ℝ) a).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian m S))
  simp only [id_eq, integral_id_multivariateGaussian] at this
  simpa using this

lemma integral_coord_mul (m : EuclideanSpace ℝ (Fin r)) {S : Matrix (Fin r) (Fin r) ℝ}
    (hS : S.PosSemidef) (a b : Fin r) :
    ∫ z, z a * z b ∂(multivariateGaussian m S) = S a b + m a * m b := by
  have h := covariance_eval_multivariateGaussian (μ := m) hS a b
  rw [covariance_eq_sub (memLp_coord m S a) (memLp_coord m S b)] at h
  simp only [integral_coord] at h
  simp only [Pi.mul_apply] at h
  linarith

lemma gaussian_prob (m : Fin r → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) :
    IsProbabilityMeasure (gaussian m S) := by
  unfold gaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma integral_gaussian (m : Fin r → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (f : (Fin r → ℝ) → ℝ)
    (hf : Continuous f) :
    ∫ ξ, f ξ ∂(gaussian m S) = ∫ z, f (WithLp.ofLp z) ∂(multivariateGaussian (WithLp.toLp 2 m) S) := by
  unfold gaussian
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable]

lemma g_memLp (m : Fin r → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (a : Fin r) :
    MemLp (fun ξ : Fin r → ℝ => ξ a) 2 (gaussian m S) := by
  unfold gaussian
  rw [memLp_map_measure_iff (continuous_apply a).aestronglyMeasurable (by fun_prop)]
  exact memLp_coord _ S a

lemma g_int (m : Fin r → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (a : Fin r) :
    ∫ ξ, ξ a ∂(gaussian m S) = m a := by
  rw [integral_gaussian m S _ (continuous_apply a), integral_coord]

lemma g_int_mul (m : Fin r → ℝ) {S : Matrix (Fin r) (Fin r) ℝ} (hS : S.PosSemidef) (a c : Fin r) :
    ∫ ξ, ξ a * ξ c ∂(gaussian m S) = S a c + m a * m c := by
  rw [integral_gaussian m S _ (by fun_prop), integral_coord_mul _ hS]

lemma g_integrable (m : Fin r → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (a : Fin r) :
    Integrable (fun ξ : Fin r → ℝ => ξ a) (gaussian m S) := by
  have := gaussian_prob m S
  exact (g_memLp m S a).integrable one_le_two

lemma g_integrable_mul (m : Fin r → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (a c : Fin r) :
    Integrable (fun ξ : Fin r → ℝ => ξ a * ξ c) (gaussian m S) :=
  (g_memLp m S a).integrable_mul (g_memLp m S c)

end RhsExtG


open MeasureTheory ProbabilityTheory Matrix MinimaxSLP.ObjSDP MinimaxSLP.RhsExtremal

namespace RhsExtG

variable {r : ℕ}

/-- one mixture component. -/
noncomputable def blk (b : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) : Measure (Fin r → ℝ) :=
  ENNReal.ofReal b.2.2 • gaussian (b.2.2⁻¹ • b.2.1) ((b.2.2 ^ 2)⁻¹ • (b.2.2 • b.1 - vecMulVec b.2.1 b.2.1))

lemma mixture_eq {K N : ℕ} (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)) :
    mixture s = ∑ k, ∑ i, blk (s k i) := rfl

lemma cov_psd {V : Matrix (Fin r) (Fin r) ℝ} {v : Fin r → ℝ} {w : ℝ}
    (hb : (bordered V v w).PosSemidef) (hw : 0 < w) :
    ((w ^ 2)⁻¹ • (w • V - vecMulVec v v)).PosSemidef := by
  refine PosSemidef.smul ?_ (by positivity)
  have hV := RhsExtH.bord_symm hb
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun a => ?_⟩
  · rw [isHermitian_iff_isSymm]
    refine IsSymm.sub (hV.smul w) ?_
    unfold IsSymm; rw [transpose_vecMulVec]
  · rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, vecMulVec_mulVec]
    have e : a ⬝ᵥ (MulOpposite.op (v ⬝ᵥ a) • v) = (v ⬝ᵥ a) * (v ⬝ᵥ a) := by
      rw [dotProduct_comm]; simp [smul_dotProduct, dotProduct_comm]
    rw [e, smul_eq_mul]
    have hq := RhsExtH.bord_quad_nonneg hb a (-(v ⬝ᵥ a) / w)
    have e2 : 2 * (-(v ⬝ᵥ a) / w) * (v ⬝ᵥ a) + (-(v ⬝ᵥ a) / w) ^ 2 * w = -((v ⬝ᵥ a) * (v ⬝ᵥ a)) / w := by
      field_simp; ring
    have : 0 ≤ a ⬝ᵥ (V *ᵥ a) - (v ⬝ᵥ a) * (v ⬝ᵥ a) / w := by
      have := hq; rw [add_assoc, e2] at this; linarith [this, neg_div w ((v ⬝ᵥ a) * (v ⬝ᵥ a))]
    have h3 : 0 ≤ w * (a ⬝ᵥ (V *ᵥ a) - (v ⬝ᵥ a) * (v ⬝ᵥ a) / w) := mul_nonneg hw.le this
    have : w * (a ⬝ᵥ (V *ᵥ a) - (v ⬝ᵥ a) * (v ⬝ᵥ a) / w) = w * (a ⬝ᵥ (V *ᵥ a)) - (v ⬝ᵥ a) * (v ⬝ᵥ a) := by
      field_simp
    linarith

lemma blk_general (b : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) (hw : 0 ≤ b.2.2)
    (f : (Fin r → ℝ) → ℝ)
    (hf : Integrable f (gaussian (b.2.2⁻¹ • b.2.1) ((b.2.2 ^ 2)⁻¹ • (b.2.2 • b.1 - vecMulVec b.2.1 b.2.1)))) :
    Integrable f (blk b) ∧ ∫ ξ, f ξ ∂(blk b) =
      b.2.2 * ∫ ξ, f ξ ∂(gaussian (b.2.2⁻¹ • b.2.1) ((b.2.2 ^ 2)⁻¹ • (b.2.2 • b.1 - vecMulVec b.2.1 b.2.1))) := by
  refine ⟨hf.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  rw [blk, integral_smul_measure, ENNReal.toReal_ofReal hw, smul_eq_mul]

lemma blk_univ (b : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :
    blk b Set.univ = ENNReal.ofReal b.2.2 := by
  have := gaussian_prob (b.2.2⁻¹ • b.2.1) ((b.2.2 ^ 2)⁻¹ • (b.2.2 • b.1 - vecMulVec b.2.1 b.2.1))
  simp [blk]

lemma blk_w_nonneg (b : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) (hpos : 0 < b.2.2 ∨ b = 0) :
    0 ≤ b.2.2 := by
  rcases hpos with h | rfl
  · exact h.le
  · simp

lemma blk_coord (b : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) (hpos : 0 < b.2.2 ∨ b = 0) (a : Fin r) :
    Integrable (fun ξ : Fin r → ℝ => ξ a) (blk b) ∧ ∫ ξ, ξ a ∂(blk b) = b.2.1 a := by
  obtain ⟨h1, h2⟩ := blk_general b (blk_w_nonneg b hpos) _ (g_integrable _ _ a)
  refine ⟨h1, ?_⟩
  rw [h2, g_int]
  rcases hpos with h | rfl
  · simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  · simp

lemma blk_coord_mul (b : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)
    (hb : (bordered b.1 b.2.1 b.2.2).PosSemidef) (hpos : 0 < b.2.2 ∨ b = 0) (a c : Fin r) :
    Integrable (fun ξ : Fin r → ℝ => ξ a * ξ c) (blk b) ∧ ∫ ξ, ξ a * ξ c ∂(blk b) = b.1 a c := by
  obtain ⟨h1, h2⟩ := blk_general b (blk_w_nonneg b hpos) _ (g_integrable_mul _ _ a c)
  refine ⟨h1, ?_⟩
  rw [h2]
  rcases hpos with h | rfl
  · rw [g_int_mul _ (cov_psd hb h)]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.sub_apply, vecMulVec_apply]
    field_simp; ring
  · simp

lemma blk_sq (b : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) (hpos : 0 < b.2.2 ∨ b = 0) (a : Fin r) :
    Integrable (fun ξ : Fin r → ℝ => ξ a ^ 2) (blk b) := by
  have := (blk_general b (blk_w_nonneg b hpos) _ (g_integrable_mul _ _ a a)).1
  simpa [sq] using this

theorem M4 {K N : ℕ} (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ))
    (hs : s ∈ feasible16 K N μ Q)
    (hpos : ∀ k i, 0 < (s k i).2.2 ∨ s k i = 0) :
    mixture s ∈ MinimaxSLP.ObjSDP.momentClass μ Q := by
  obtain ⟨⟨hV, hv, hw⟩, hpsd⟩ := (RhsExtH.feas_iff μ Q s).mp hs
  rw [mixture_eq]
  have hint : ∀ f : (Fin r → ℝ) → ℝ, (∀ k i, Integrable f (blk (s k i))) →
      Integrable f (∑ k, ∑ i, blk (s k i)) ∧
        ∫ ξ, f ξ ∂(∑ k, ∑ i, blk (s k i)) = ∑ k, ∑ i, ∫ ξ, f ξ ∂(blk (s k i)) := by
    intro f hf
    refine ⟨integrable_finsetSum_measure.mpr fun k _ => integrable_finsetSum_measure.mpr
      fun i _ => hf k i, ?_⟩
    rw [integral_finsetSum_measure fun k _ => integrable_finsetSum_measure.mpr fun i _ => hf k i]
    exact Finset.sum_congr rfl fun k _ => integral_finsetSum_measure fun i _ => hf k i
  refine ⟨⟨⟨?_⟩, fun a => ?_⟩, ?_, ?_⟩
  · rw [Measure.coe_finset_sum, Finset.sum_apply]
    simp only [Measure.coe_finset_sum, Finset.sum_apply, blk_univ]
    rw [← ENNReal.ofReal_one, ← hw]
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => Finset.sum_nonneg fun i _ => blk_w_nonneg _ (hpos k i)]
    exact Finset.sum_congr rfl fun k _ =>
      (ENNReal.ofReal_sum_of_nonneg fun i _ => blk_w_nonneg _ (hpos k i)).symm
  · rw [memLp_two_iff_integrable_sq (continuous_apply a).aestronglyMeasurable]
    exact (hint _ fun k i => blk_sq _ (hpos k i) a).1
  · ext a
    unfold MomentDRO.Conf.meanVec
    rw [(hint _ fun k i => (blk_coord _ (hpos k i) a).1).2, ← hv]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => (blk_coord _ (hpos k i) a).2
  · ext a c
    unfold MomentDRO.Conf.secondMomentAbout
    simp only [Matrix.of_apply, Pi.zero_apply, sub_zero]
    rw [(hint _ fun k i => (blk_coord_mul _ (hpsd k i) (hpos k i) a c).1).2, ← hV]
    simp only [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
      (blk_coord_mul _ (hpsd k i) (hpos k i) a c).2

end RhsExtG


open MeasureTheory Matrix MinimaxSLP.RhsExtremal

namespace RhsExtU

variable {r d n K N : ℕ}

def aff (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (x : Fin n → ℝ) (p : Fin K × Fin N) (h : Fin r → ℝ) : ℝ :=
  α p.1 * ((h - T *ᵥ x) ⬝ᵥ ps p.2) + β p.1

lemma aff_eq (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (x : Fin n → ℝ) (p : Fin K × Fin N) (h : Fin r → ℝ) :
    aff T α β ps x p h = α p.1 * (ps p.2 ⬝ᵥ h) + (β p.1 - α p.1 * (ps p.2 ⬝ᵥ (T *ᵥ x))) := by
  unfold aff; rw [sub_dotProduct, dotProduct_comm h, dotProduct_comm (T *ᵥ x)]; ring

lemma lin_integral (ν : Measure (Fin r → ℝ)) [IsFiniteMeasure ν]
    (hc : ∀ a, Integrable (fun ξ : Fin r → ℝ => ξ a) ν) (c : Fin r → ℝ) (e : ℝ) :
    Integrable (fun h => c ⬝ᵥ h + e) ν ∧
      ∫ h, (c ⬝ᵥ h + e) ∂ν = c ⬝ᵥ (fun a => ∫ ξ, ξ a ∂ν) + ν.real Set.univ * e := by
  have h1 : Integrable (fun h : Fin r → ℝ => c ⬝ᵥ h) ν := by
    simp only [dotProduct]
    exact integrable_finset_sum _ fun a _ => (hc a).const_mul (c a)
  refine ⟨h1.add (integrable_const e), ?_⟩
  rw [integral_add h1 (integrable_const e), integral_const, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  rw [integral_finset_sum _ fun a _ => (hc a).const_mul (c a)]
  exact Finset.sum_congr rfl fun a _ => integral_const_mul _ _

variable [NeZero K]

lemma U_facts (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) :
    Nonempty (Fin N) ∧
    (∀ h p, aff T α β ps x p h ≤ MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) ∧
    (∀ h, ∃ p, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) = aff T α β ps x p h) := by
  have H := fun h => (disutility_Qval_eq_max_pairs W T q α β ps hα hA2 hA3 hA5 x h).2
  refine ⟨?_, fun h p => (H h).2 ⟨p, rfl⟩, fun h => ?_⟩
  · obtain ⟨⟨p, -⟩, -⟩ := H 0; exact ⟨p.2⟩
  · obtain ⟨p, hp⟩ := (H h).1; exact ⟨p, hp.symm⟩

lemma U_eq_sup (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) (hne : (Finset.univ : Finset (Fin K × Fin N)).Nonempty) :
    (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) =
      fun h => Finset.univ.sup' hne (fun p => aff T α β ps x p h) := by
  obtain ⟨-, hle, hex⟩ := U_facts W T q α β ps hα hA2 hA3 hA5 x
  funext h
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hex h
    rw [hp]; exact Finset.le_sup' (fun p => aff T α β ps x p h) (Finset.mem_univ p)
  · exact Finset.sup'_le _ _ fun p _ => hle h p

lemma U_integrable (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) (ν : Measure (Fin r → ℝ)) [IsFiniteMeasure ν]
    (hc : ∀ a, Integrable (fun ξ : Fin r → ℝ => ξ a) ν) :
    Integrable (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) ν := by
  obtain ⟨hN, hle, hex⟩ := U_facts W T q α β ps hα hA2 hA3 hA5 x
  have hne : (Finset.univ : Finset (Fin K × Fin N)).Nonempty := Finset.univ_nonempty
  have haff : ∀ p, Integrable (aff T α β ps x p) ν := by
    intro p
    have := (lin_integral ν hc (α p.1 • ps p.2) (β p.1 - α p.1 * (ps p.2 ⬝ᵥ (T *ᵥ x)))).1
    refine this.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [aff_eq, smul_dotProduct, smul_eq_mul]
  have hcont : Continuous (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) := by
    rw [U_eq_sup W T q α β ps hα hA2 hA3 hA5 x hne]
    refine Continuous.finset_sup'_apply hne fun p _ => ?_
    unfold aff; simp only [dotProduct]; fun_prop
  refine Integrable.mono' (g := fun h => ∑ p, |aff T α β ps x p h|)
    (integrable_finset_sum _ fun p _ => (haff p).abs) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  obtain ⟨p, hp⟩ := hex h
  rw [Real.norm_eq_abs, hp]
  exact Finset.single_le_sum (f := fun p => |aff T α β ps x p h|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ p)

end RhsExtU


open MeasureTheory ProbabilityTheory Matrix MinimaxSLP.ObjSDP MinimaxSLP.RhsExtremal

namespace RhsExtG

variable {r : ℕ}

lemma blk_finite (b : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) : IsFiniteMeasure (blk b) :=
  ⟨by rw [blk_univ]; exact ENNReal.ofReal_lt_top⟩

theorem M5 {d n K N : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ)
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ))
    (hs : s ∈ feasible16 K N μ Q)
    (hpos : ∀ k i, 0 < (s k i).2.2 ∨ s k i = 0) :
    Integrable (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) (mixture s) ∧
    obj16 T α β ps x s ≤ ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂(mixture s) := by
  set U := fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) with hU
  obtain ⟨-, hle, -⟩ := RhsExtU.U_facts W T q α β ps hα hA2 hA3 hA5 x
  have hUi : ∀ k i, Integrable U (blk (s k i)) := by
    intro k i
    have := blk_finite (s k i)
    exact RhsExtU.U_integrable W T q α β ps hα hA2 hA3 hA5 x _
      fun a => (blk_coord _ (hpos k i) a).1
  rw [mixture_eq]
  refine ⟨integrable_finsetSum_measure.mpr fun k _ => integrable_finsetSum_measure.mpr
      fun i _ => hUi k i, ?_⟩
  rw [integral_finsetSum_measure fun k _ => integrable_finsetSum_measure.mpr fun i _ => hUi k i]
  unfold obj16
  refine Finset.sum_le_sum fun k _ => ?_
  rw [integral_finsetSum_measure fun i _ => hUi k i]
  refine Finset.sum_le_sum fun i _ => ?_
  have := blk_finite (s k i)
  have hc : ∀ a, Integrable (fun ξ : Fin r → ℝ => ξ a) (blk (s k i)) :=
    fun a => (blk_coord _ (hpos k i) a).1
  obtain ⟨hli, hlint⟩ := RhsExtU.lin_integral (blk (s k i)) hc (α k • ps i)
    (β k - α k * (ps i ⬝ᵥ (T *ᵥ x)))
  have hmean : (fun a => ∫ ξ, ξ a ∂(blk (s k i))) = (s k i).2.1 :=
    funext fun a => (blk_coord _ (hpos k i) a).2
  have hreal : (blk (s k i)).real Set.univ = (s k i).2.2 := by
    rw [measureReal_def, blk_univ, ENNReal.toReal_ofReal (blk_w_nonneg _ (hpos k i))]
  rw [hmean, hreal] at hlint
  have key : α k * (ps i ⬝ᵥ (s k i).2.1) + (s k i).2.2 * (β k - α k * (ps i ⬝ᵥ (T *ᵥ x))) =
      ∫ h, ((α k • ps i) ⬝ᵥ h + (β k - α k * (ps i ⬝ᵥ (T *ᵥ x)))) ∂(blk (s k i)) := by
    rw [hlint, smul_dotProduct, smul_eq_mul]
  rw [key]
  refine integral_mono hli (hUi k i) fun h => ?_
  have := hle h (k, i)
  rw [RhsExtU.aff_eq] at this
  simp only [smul_dotProduct, smul_eq_mul, U]
  exact this

end RhsExtG

theorem solution {r d n K N : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ)
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ))
    (hs : s ∈ feasible16 K N μ Q)
    (hpos : ∀ k i, 0 < (s k i).2.2 ∨ s k i = 0) :
    Integrable (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) (mixture s) ∧
    obj16 T α β ps x s ≤ ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂(mixture s) :=
  RhsExtG.M5 W T q α β ps μ Q hα hA2 hA3 hA5 x s hs hpos
