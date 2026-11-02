-- Prove2me | solution 1 for NetworkVolatility.Robust.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:35:01.918024+00:00
-- url     : https://prove2.me/submissions/a7e12a54-681e-4bd5-b755-5b05681e1955

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

open Matrix
open scoped Matrix.Norms.L2Operator
open NetworkVolatility.Robust

namespace NVSol

lemma dd_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma eq_zero_of_dd_le {n : ℕ} (v : Fin n → ℝ) (h : v ⬝ᵥ v ≤ 0) : v = 0 :=
  dotProduct_self_eq_zero.mp (le_antisymm h (dd_nonneg v))

/-- the quadratic form `yᵀ(I - αV)y`. -/
def Q {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (y : Fin n → ℝ) : ℝ :=
  y ⬝ᵥ y - α * (y ⬝ᵥ (V *ᵥ y))

lemma Q_eq {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (y : Fin n → ℝ) :
    Q V α y = y ⬝ᵥ (y - α • (V *ᵥ y)) := by
  simp [Q, dotProduct_sub, dotProduct_smul, smul_eq_mul]

lemma Q_smul {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α t : ℝ) (y : Fin n → ℝ) :
    Q V α (t • y) = t ^ 2 * Q V α y := by
  simp [Q, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

lemma util_update {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x : Fin n → ℝ)
    (i : Fin n) (hd : V i i = 0) (y : ℝ) :
    utility V α b p (Function.update x i y) i =
      -(1/2) * y ^ 2 + (b i - p i + α * (V *ᵥ x) i) * y := by
  have h1 : (V *ᵥ x) i = ∑ j ∈ Finset.univ.erase i, V i j * x j := by
    rw [Matrix.mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp [hd]
  have hs : ∑ j ∈ Finset.univ.erase i,
      V i j * (Function.update x i y) i * (Function.update x i y) j = y * (V *ᵥ x) i := by
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Function.update_of_ne this]; ring
  unfold utility; rw [hs]; simp; ring

lemma isEq_iff {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x : Fin n → ℝ)
    (hd : ∀ i, V i i = 0) :
    IsConsumptionEq V α b p x ↔ ∀ i, 0 ≤ x i ∧ ∀ y : ℝ, 0 ≤ y →
      -(1/2) * y ^ 2 + (b i - p i + α * (V *ᵥ x) i) * y ≤
        -(1/2) * (x i) ^ 2 + (b i - p i + α * (V *ᵥ x) i) * x i := by
  unfold IsConsumptionEq
  refine forall_congr' (fun i => and_congr Iff.rfl (forall_congr' fun y => imp_congr Iff.rfl ?_))
  rw [util_update V α b p x i (hd i) y]
  have := util_update V α b p x i (hd i) (x i)
  rw [Function.update_eq_self] at this
  rw [this]

lemma compl {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x : Fin n → ℝ)
    (hd : ∀ i, V i i = 0) (h : IsConsumptionEq V α b p x) (i : Fin n) :
    0 ≤ x i ∧ (b i - p i + α * (V *ᵥ x) i) ≤ x i ∧
      x i * (x i - (b i - p i + α * (V *ᵥ x) i)) = 0 := by
  obtain ⟨h0, hy⟩ := (isEq_iff V α b p x hd).mp h i
  set a := b i - p i + α * (V *ᵥ x) i
  by_cases ha : 0 ≤ a
  · have := hy a ha
    have hx : x i = a := by nlinarith [sq_nonneg (x i - a)]
    refine ⟨h0, hx.ge, ?_⟩; rw [hx]; ring
  · have := hy 0 le_rfl
    push Not at ha
    have hx : x i = 0 := by nlinarith
    refine ⟨h0, by rw [hx]; exact ha.le, by rw [hx]; ring⟩

lemma isEq_of_interior {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x : Fin n → ℝ)
    (hd : ∀ i, V i i = 0) (hx : ∀ i, 0 ≤ x i) (hL : x - α • (V *ᵥ x) = b - p) :
    IsConsumptionEq V α b p x := by
  rw [isEq_iff V α b p x hd]
  intro i
  have hi := congrFun hL i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  have ha : b i - p i + α * (V *ᵥ x) i = x i := by linarith
  refine ⟨hx i, fun y _ => ?_⟩
  rw [ha]; nlinarith [sq_nonneg (y - x i)]

lemma revenue_eq {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x : Fin n → ℝ) (c : ℝ)
    (hd : ∀ i, V i i = 0) (h : IsConsumptionEq V α b p x) :
    revenue c p x = 2 * (x ⬝ᵥ (fun i => (b i - c) / 2)) - Q V α x := by
  rw [Q_eq]
  unfold revenue
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := (compl V α b p x hd h i).2.2
  linarith

lemma price_eq {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x : Fin n → ℝ)
    (hd : ∀ i, V i i = 0) (h : IsConsumptionEq V α b p x) (i : Fin n) (hi : 0 < x i) :
    p i = b i - (x - α • (V *ᵥ x)) i := by
  have := (compl V α b p x hd h i).2.2
  have h2 : x i - (b i - p i + α * (V *ᵥ x) i) = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- coercivity -/
def Coer {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : Prop :=
  ∃ m > 0, ∀ y : Fin n → ℝ, m * (y ⬝ᵥ y) ≤ Q V α y

lemma eq_zero_of_Q_le {n : ℕ} {V : Matrix (Fin n) (Fin n) ℝ} {α : ℝ} (hC : Coer V α)
    (y : Fin n → ℝ) (h : Q V α y ≤ 0) : y = 0 := by
  obtain ⟨m, hm, hQ⟩ := hC
  apply eq_zero_of_dd_le
  have := hQ y
  by_contra hc; push Not at hc
  nlinarith

lemma uniq {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x y : Fin n → ℝ)
    (hd : ∀ i, V i i = 0) (hC : Coer V α) (hx : IsConsumptionEq V α b p x)
    (hy : IsConsumptionEq V α b p y) : x = y := by
  have key : Q V α (x - y) = ∑ i, (x i - y i) *
      ((x i - (b i - p i + α * (V *ᵥ x) i)) - (y i - (b i - p i + α * (V *ᵥ y) i))) := by
    rw [Q_eq]
    simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_sub]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hle : Q V α (x - y) ≤ 0 := by
    rw [key]
    refine Finset.sum_nonpos (fun i _ => ?_)
    obtain ⟨h1, h2, h3⟩ := compl V α b p x hd hx i
    obtain ⟨k1, k2, k3⟩ := compl V α b p y hd hy i
    nlinarith [mul_nonneg h1 (sub_nonneg.mpr k2), mul_nonneg k1 (sub_nonneg.mpr h2)]
  exact sub_eq_zero.mp (eq_zero_of_Q_le hC _ hle)

lemma solve {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hC : Coer V α) (g : Fin n → ℝ) :
    ∃ x, x - α • (V *ᵥ x) = g := by
  set L : Matrix (Fin n) (Fin n) ℝ := 1 - α • V
  have hLx : ∀ x, L *ᵥ x = x - α • (V *ᵥ x) := by
    intro x; simp [L, sub_mulVec, smul_mulVec]
  have hdet : L.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hLv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv
    apply eq_zero_of_Q_le hC
    rw [Q_eq, ← hLx, hLv]; simp
  refine ⟨L⁻¹ *ᵥ g, ?_⟩
  rw [← hLx, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hdet), one_mulVec]

lemma mulVec_nn {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (hV : ∀ i j, 0 ≤ V i j)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (i : Fin n) : 0 ≤ (V *ᵥ w) i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hV i j) (hw j))

lemma pos_sol {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hV : ∀ i j, 0 ≤ V i j) (hC : Coer V α) (g x : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hx : x - α • (V *ᵥ x) = g) : ∀ i, g i ≤ x i := by
  set z : Fin n → ℝ := fun i => max (-x i) 0
  set w : Fin n → ℝ := fun i => max (x i) 0
  have hxw : x = w - z := by
    ext i; simp only [w, z, Pi.sub_apply]
    rcases le_total 0 (x i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hz0 : ∀ i, 0 ≤ z i := fun i => le_max_right _ _
  have hw0 : ∀ i, 0 ≤ w i := fun i => le_max_right _ _
  have hzx : z ⬝ᵥ x = -(z ⬝ᵥ z) := by
    simp only [dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [z]
    rcases le_total 0 (x i) with h | h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_left (by linarith)]; ring
  have hzVw : 0 ≤ z ⬝ᵥ (V *ᵥ w) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hz0 i) (mulVec_nn V hV w hw0 i))
  have hzg : 0 ≤ z ⬝ᵥ g := Finset.sum_nonneg (fun i _ => mul_nonneg (hz0 i) (hg i))
  have hcalc : z ⬝ᵥ g = -(Q V α z) - α * (z ⬝ᵥ (V *ᵥ w)) := by
    rw [← hx, Q]
    conv_lhs => rw [dotProduct_sub, dotProduct_smul, hzx, smul_eq_mul, hxw, mulVec_sub,
      dotProduct_sub]
    ring
  have hQz : Q V α z ≤ 0 := by nlinarith [mul_nonneg hα hzVw]
  have hz : z = 0 := eq_zero_of_Q_le hC z hQz
  have hxnn : ∀ i, 0 ≤ x i := by
    intro i
    have : z i = 0 := by rw [hz]; rfl
    simp only [z] at this
    by_contra hc; push Not at hc
    have : max (-x i) 0 = -x i := max_eq_left (by linarith)
    linarith
  intro i
  have hi := congrFun hx i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  have : 0 ≤ (V *ᵥ x) i := mulVec_nn V hV x hxnn i
  nlinarith [mul_nonneg hα this]

lemma symm_dot {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (hV : V.IsSymm) (u w : Fin n → ℝ) :
    u ⬝ᵥ (V *ᵥ w) = w ⬝ᵥ (V *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hV.eq, dotProduct_comm]

/-- completing the square -/
lemma complete_sq {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hV : V.IsSymm)
    (f xs : Fin n → ℝ) (hxs : xs - α • (V *ᵥ xs) = f) (y : Fin n → ℝ) :
    xs ⬝ᵥ f - (2 * (y ⬝ᵥ f) - Q V α y) = Q V α (y - xs) := by
  have hs := symm_dot V hV y xs
  have hc := dotProduct_comm y xs
  rw [← hxs]
  simp only [Q, dotProduct_sub, sub_dotProduct, mulVec_sub, dotProduct_smul, smul_eq_mul]
  rw [hs, hc]; ring


lemma quad_abs_le {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    |y ⬝ᵥ (D *ᵥ y)| ≤ ‖D‖ * (y ⬝ᵥ y) := by
  set e : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm y
  have h1 := D.l2_opNorm_mulVec e
  have hin : y ⬝ᵥ (D *ᵥ y) = inner ℝ e ((EuclideanSpace.equiv (Fin n) ℝ).symm (D *ᵥ e)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [e, dotProduct_comm]
  have hn : ‖e‖ ^ 2 = y ⬝ᵥ y := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp [e]
  rw [hin, ← hn]
  calc _ ≤ ‖e‖ * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (D *ᵥ e)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖e‖ * (‖D‖ * ‖e‖) := by gcongr
    _ = ‖D‖ * ‖e‖ ^ 2 := by ring


lemma Q_nonneg {n : ℕ} {V : Matrix (Fin n) (Fin n) ℝ} {α : ℝ} (hC : Coer V α) (y : Fin n → ℝ) :
    0 ≤ Q V α y := by
  obtain ⟨m, hm, hQ⟩ := hC
  exact le_trans (mul_nonneg hm.le (dd_nonneg y)) (hQ y)

lemma lamMax_eq_norm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    lamMax M = ‖M‖ := by
  have hsa : IsSelfAdjoint M := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hM
  rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℝ) with h | h
  · have : M = 0 := Subsingleton.elim _ _
    subst this
    have : spectrum ℝ (0 : Matrix (Fin n) (Fin n) ℝ) = ∅ := by
      ext x; simp
    simp [lamMax]
  · have := IsGreatest.norm_cfc (𝕜 := ℝ) (fun x => x) M (by fun_prop) hsa
    rw [cfc_id' ℝ M] at this
    unfold lamMax
    simpa [Real.norm_eq_abs] using this.csSup_eq

lemma perron {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ i j, 0 ≤ W i j) (hsym : W.IsSymm)
    (hpos : 0 < ‖W‖) :
    ∃ v : Fin n → ℝ, (∀ i, 0 ≤ v i) ∧ v ≠ 0 ∧ W *ᵥ v = ‖W‖ • v := by
  have hsa : IsSelfAdjoint W := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℝ) with h | h
  · have : W = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at hpos; exact absurd hpos (lt_irrefl _)
  have hG := IsGreatest.norm_cfc (𝕜 := ℝ) (fun x => x) W (by fun_prop) hsa
  rw [cfc_id' ℝ W] at hG
  obtain ⟨μ, hμ, hμn⟩ := hG.1
  simp only [Real.norm_eq_abs] at hμn
  -- eigenvector
  have hdet : (algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) μ - W).det = 0 := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hμ
    exact hμ
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hWx : W *ᵥ x = μ • x := by
    rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hx
    exact hx.symm
  set ℓ := ‖W‖
  set v : Fin n → ℝ := fun i => |x i|
  have hvv : v ⬝ᵥ v = x ⬝ᵥ x := by
    simp only [dotProduct, v]
    exact Finset.sum_congr rfl (fun i _ => abs_mul_abs_self (x i))
  have hxWx : x ⬝ᵥ (W *ᵥ x) = μ * (x ⬝ᵥ x) := by rw [hWx, dotProduct_smul, smul_eq_mul]
  have habs : |x ⬝ᵥ (W *ᵥ x)| ≤ v ⬝ᵥ (W *ᵥ v) := by
    simp only [dotProduct, mulVec, v, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul, abs_mul, abs_of_nonneg (hW i j)]
  have hv1 : ℓ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (W *ᵥ v) := by
    rw [hvv, ← hμn, ← abs_of_nonneg (dd_nonneg x), ← abs_mul, ← hxWx]; exact habs
  have hQW : ∀ y, y ⬝ᵥ (W *ᵥ y) ≤ ℓ * (y ⬝ᵥ y) :=
    fun y => (le_abs_self _).trans (quad_abs_le W y)
  set φ : (Fin n → ℝ) → ℝ := fun y => ℓ * (y ⬝ᵥ y) - y ⬝ᵥ (W *ᵥ y)
  have hφ : ∀ y, 0 ≤ φ y := fun y => by simp only [φ]; linarith [hQW y]
  have hφv : φ v = 0 := le_antisymm (by simp only [φ]; linarith) (hφ v)
  set w := ℓ • v - W *ᵥ v with hwd
  have hwdef : w ⬝ᵥ w = ℓ * (w ⬝ᵥ v) - w ⬝ᵥ (W *ᵥ v) := by
    conv_lhs => rw [hwd]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  clear_value w
  have hexp : ∀ t : ℝ, φ (v + t • w) = φ v + 2 * t * (w ⬝ᵥ w) + t ^ 2 * φ w := by
    intro t
    have hs := symm_dot W hsym v w
    have hc := dotProduct_comm v w
    simp only [φ, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    linear_combination (t * ℓ) * hc - t * hs - 2 * t * hwdef
  have hww : w ⬝ᵥ w ≤ 0 := by
    set a := w ⬝ᵥ w
    set c := φ w
    have hc0 : 0 ≤ c := hφ w
    have h := hφ (v + (-a / (c + 1)) • w)
    rw [hexp, hφv] at h
    have hc1 : 0 < c + 1 := by linarith
    have : 0 ≤ -(a ^ 2 * (c + 2)) := by
      have e : (0 : ℝ) + 2 * (-a / (c + 1)) * a + (-a / (c + 1)) ^ 2 * c
          = -(a ^ 2 * (c + 2)) / (c + 1) ^ 2 := by field_simp; ring
      rw [e] at h
      exact (div_nonneg_iff.mp h).elim (fun h => h.1) (fun h => by
        have := h.2; nlinarith [sq_nonneg (c+1)])
    nlinarith [sq_nonneg a, dd_nonneg w]
  have hw : w = 0 := eq_zero_of_dd_le w hww
  refine ⟨v, fun i => abs_nonneg _, ?_, ?_⟩
  · intro hv; apply hx0; funext i
    have := congrFun hv i; simpa [v] using this
  · rw [hwd] at hw; exact (sub_eq_zero.mp hw).symm

lemma pert {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ) (α ε : ℝ) (hα : 0 ≤ α)
    (hWt : Wt ∈ uncSet W ε) (y : Fin n → ℝ) :
    |Q Wt α y - Q W α y| ≤ α * ε * ‖W‖ * (y ⬝ᵥ y) := by
  have h := quad_abs_le (Wt - W) y
  rw [sub_mulVec, dotProduct_sub] at h
  have hn : ‖Wt - W‖ ≤ ε * ‖W‖ := by rw [norm_sub_rev]; exact hWt.1
  have e : |Q Wt α y - Q W α y| = α * |y ⬝ᵥ (Wt *ᵥ y) - y ⬝ᵥ (W *ᵥ y)| := by
    unfold Q
    rw [show y ⬝ᵥ y - α * (y ⬝ᵥ (Wt *ᵥ y)) - (y ⬝ᵥ y - α * (y ⬝ᵥ (W *ᵥ y)))
      = (-α) * (y ⬝ᵥ (Wt *ᵥ y) - y ⬝ᵥ (W *ᵥ y)) by ring, abs_mul, abs_neg, abs_of_nonneg hα]
  rw [e]
  have := mul_le_mul_of_nonneg_right hn (dd_nonneg y)
  calc _ ≤ α * (‖Wt - W‖ * (y ⬝ᵥ y)) := mul_le_mul_of_nonneg_left h hα
    _ ≤ α * (ε * ‖W‖ * (y ⬝ᵥ y)) := mul_le_mul_of_nonneg_left this hα
    _ = _ := by ring

lemma ratio_bound {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ) (α m d : ℝ) (hm : 0 < m)
    (hd : 0 ≤ d) (hmd : 0 < m - d) (hsW : W.IsSymm) (hsWt : Wt.IsSymm)
    (hQ : ∀ y, m * (y ⬝ᵥ y) ≤ Q W α y) (hP : ∀ y, |Q Wt α y - Q W α y| ≤ d * (y ⬝ᵥ y))
    (f xs xt : Fin n → ℝ) (hxs : xs - α • (W *ᵥ xs) = f) (hxt : xt - α • (Wt *ᵥ xt) = f) :
    |xs ⬝ᵥ f - xt ⬝ᵥ f| / (xs ⬝ᵥ f) ≤ d / (m - d) := by
  set A := xs ⬝ᵥ f
  set B := xt ⬝ᵥ f
  have hA : Q W α xs = A := by rw [Q_eq, hxs]
  have hB : Q Wt α xt = B := by rw [Q_eq, hxt]
  have hQt : ∀ y, (m - d) * (y ⬝ᵥ y) ≤ Q Wt α y := fun y => by
    have := hP y; have := hQ y; rw [abs_le] at *; nlinarith
  have hCt : Coer Wt α := ⟨m - d, hmd, hQt⟩
  have hCW : Coer W α := ⟨m, hm, hQ⟩
  have hA0 : 0 ≤ A := hA ▸ Q_nonneg hCW xs
  -- lower bound on B
  have h_low : m * A ≤ (m + d) * B := by
    set t := m / (m + d)
    have ht : t * (m + d) = m := by simp only [t]; field_simp
    have ht0 : 0 ≤ t := div_nonneg hm.le (by linarith)
    have c1 := complete_sq Wt α hsWt f xt hxt (t • xs)
    have c2 := Q_nonneg hCt (t • xs - xt)
    rw [Q_smul, smul_dotProduct, smul_eq_mul] at c1
    have hq : m * Q Wt α xs ≤ (m + d) * A := by
      have := hP xs; have := hQ xs; rw [abs_le] at *; nlinarith
    -- B ≥ 2 t A - t^2 q
    have H1 : 2 * (t * A) - t ^ 2 * Q Wt α xs ≤ B := by
      have : xt ⬝ᵥ f = B := rfl; linarith
    have e1 : (m + d) * (2 * (t * A) - t ^ 2 * Q Wt α xs) = 2 * m * A - t * (m * Q Wt α xs) := by
      linear_combination (2 * A - t * Q Wt α xs) * ht
    have e2 : t * ((m + d) * A) = m * A := by linear_combination A * ht
    have := mul_le_mul_of_nonneg_left H1 (by linarith : (0:ℝ) ≤ m + d)
    have := mul_le_mul_of_nonneg_left hq ht0
    linarith
  have h_up : (m - d) * B ≤ m * A := by
    set t := (m - d) / m
    have ht : t * m = m - d := by simp only [t]; field_simp
    have ht0 : 0 ≤ t := div_nonneg hmd.le hm.le
    have c1 := complete_sq W α hsW f xs hxs (t • xt)
    have c2 := Q_nonneg hCW (t • xt - xs)
    rw [Q_smul, smul_dotProduct, smul_eq_mul] at c1
    have hq : (m - d) * Q W α xt ≤ m * B := by
      have := hP xt; have := hQt xt; rw [abs_le] at *; nlinarith
    have H1 : 2 * (t * B) - t ^ 2 * Q W α xt ≤ A := by linarith
    have e1 : m * (2 * (t * B) - t ^ 2 * Q W α xt) = 2 * (m - d) * B - t * ((m - d) * Q W α xt) := by
      linear_combination (2 * B - t * Q W α xt) * ht
    have e2 : t * (m * B) = (m - d) * B := by linear_combination B * ht
    have := mul_le_mul_of_nonneg_left H1 hm.le
    have := mul_le_mul_of_nonneg_left hq ht0
    linarith
  rcases hA0.eq_or_lt with h0 | h0
  · rw [← h0, div_zero]; exact div_nonneg hd hmd.le
  · rw [div_le_div_iff₀ h0 hmd]
    rcases abs_cases (A - B) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · nlinarith [mul_le_mul_of_nonneg_left h_low hmd.le]
    · nlinarith

lemma rev_ps {n : ℕ} (b x : Fin n → ℝ) (c : ℝ) :
    revenue c (fun i => b i - (b i - c) / 2) x = x ⬝ᵥ (fun i => (b i - c) / 2) := by
  unfold revenue; simp only [dotProduct]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma opt_struct {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b : Fin n → ℝ) (c : ℝ)
    (hα : 0 ≤ α) (hWnn : ∀ i j, 0 ≤ W i j) (hWsym : W.IsSymm) (hWd : ∀ i, W i i = 0)
    (hC : Coer W α) (hA2 : Assumption2 b c) (xs : Fin n → ℝ)
    (hxs : xs - α • (W *ᵥ xs) = fun i => (b i - c) / 2) :
    IsOptimalPrice W α b c (fun i => b i - (b i - c) / 2) ∧
    (∀ p, IsOptimalPrice W α b c p → p = fun i => b i - (b i - c) / 2) ∧
    optRevenue W α b c = xs ⬝ᵥ (fun i => (b i - c) / 2) ∧ (∀ i, 0 < xs i) := by
  set f : Fin n → ℝ := fun i => (b i - c) / 2 with hfdef
  have hf : ∀ i, 0 < f i := fun i => by simp only [f]; linarith [hA2 i]
  have hpos := pos_sol W α hα hWnn hC f xs (fun i => (hf i).le) hxs
  have hxs0 : ∀ i, 0 < xs i := fun i => lt_of_lt_of_le (hf i) (hpos i)
  set ps : Fin n → ℝ := fun i => b i - (b i - c) / 2 with hps
  have hbp : b - ps = f := by ext i; simp only [Pi.sub_apply, ps, f]; ring
  have heq : IsConsumptionEq W α b ps xs :=
    isEq_of_interior W α b ps xs hWd (fun i => (hxs0 i).le) (by rw [hxs, hbp])
  have hrev : revenue c ps xs = xs ⬝ᵥ f := rev_ps b xs c
  have hG : IsGreatest (revenueSet W α b c) (xs ⬝ᵥ f) := by
    refine ⟨⟨ps, xs, heq, hrev.symm⟩, ?_⟩
    rintro r ⟨p, x, hx, rfl⟩
    rw [revenue_eq W α b p x c hWd hx]
    have h1 := complete_sq W α hWsym f xs hxs x
    have h2 := Q_nonneg hC (x - xs)
    linarith
  refine ⟨⟨xs, heq, hrev ▸ hG⟩, ?_, hG.csSup_eq, hxs0⟩
  rintro p ⟨x, hx, hxG⟩
  have hle : xs ⬝ᵥ f ≤ revenue c p x := hxG.2 hG.1
  rw [revenue_eq W α b p x c hWd hx] at hle
  have h1 := complete_sq W α hWsym f xs hxs x
  have hx' : x = xs := sub_eq_zero.mp (eq_zero_of_Q_le hC _ (by linarith))
  rw [hx'] at hx
  funext i
  rw [price_eq W α b p xs hWd hx i (hxs0 i), hxs]

lemma mem_vol {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ) (α c ε : ℝ) (b : Fin n → ℝ)
    (hα : 0 ≤ α) (hWnn : ∀ i j, 0 ≤ W i j) (hWsym : W.IsSymm) (hWd : ∀ i, W i i = 0)
    (hC : Coer W α) (hWt : Wt ∈ uncSet W ε) (hCt : Coer Wt α) (hA2 : Assumption2 b c)
    (xs xt : Fin n → ℝ) (hxs : xs - α • (W *ᵥ xs) = fun i => (b i - c) / 2)
    (hxt : xt - α • (Wt *ᵥ xt) = fun i => (b i - c) / 2) :
    |xs ⬝ᵥ (fun i => (b i - c) / 2) - xt ⬝ᵥ (fun i => (b i - c) / 2)| /
      (xs ⬝ᵥ (fun i => (b i - c) / 2)) ∈ volatilitySet W α c ε := by
  obtain ⟨hopt, -, hR, -⟩ := opt_struct W α b c hα hWnn hWsym hWd hC hA2 xs hxs
  have hf : ∀ i, 0 < (b i - c) / 2 := fun i => by linarith [hA2 i]
  have hpos := pos_sol Wt α hα hWt.2.1 hCt _ xt (fun i => (hf i).le) hxt
  have heq : IsConsumptionEq Wt α b (fun i => b i - (b i - c) / 2) xt :=
    isEq_of_interior Wt α b _ xt hWt.2.2.2 (fun i => ((hf i).trans_le (hpos i)).le)
      (by rw [hxt]; ext i; simp only [Pi.sub_apply]; ring)
  refine ⟨Wt, hWt, b, hA2, _, xt, hopt, heq, ?_⟩
  rw [hR, rev_ps]

end NVSol

open NVSol in
theorem solution {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α c ε : ℝ)
    (hS : Standing W α) (hA1 : Assumption1 W α) (hε : 0 ≤ ε)
    (h1 : α * lamMax W * (1 + ε) < 1) :
    (∀ Wt ∈ uncSet W ε, ∀ b : Fin n → ℝ, Assumption2 b c →
      (∃ p, IsOptimalPrice W α b c p) ∧
      ∀ p, IsOptimalPrice W α b c p →
        ∃ x : Fin n → ℝ, IsConsumptionEq Wt α b p x ∧ ∀ i, 0 < x i) ∧
    IsLUB (volatilitySet W α c ε) (α * lamMax W * ε / (1 - α * lamMax W * (1 + ε))) := by
  obtain ⟨hα, hWnn, hWsym, hWd⟩ := hS
  rw [lamMax_eq_norm W hWsym] at h1 ⊢
  set ℓ := ‖W‖ with hℓdef
  have hℓ0 : 0 ≤ ℓ := norm_nonneg _
  have hαℓ : 0 ≤ α * ℓ := mul_nonneg hα hℓ0
  have hm : 0 < 1 - α * ℓ := by nlinarith [mul_nonneg hαℓ hε]
  have hmd : 0 < (1 - α * ℓ) - α * ε * ℓ := by nlinarith
  have hd : 0 ≤ α * ε * ℓ := by positivity
  have hQW : ∀ y, (1 - α * ℓ) * (y ⬝ᵥ y) ≤ Q W α y := fun y => by
    have h := (le_abs_self _).trans (quad_abs_le W y)
    unfold Q; nlinarith [mul_le_mul_of_nonneg_left h hα]
  have hCW : Coer W α := ⟨_, hm, hQW⟩
  have hP : ∀ Wt ∈ uncSet W ε, ∀ y, |Q Wt α y - Q W α y| ≤ α * ε * ℓ * (y ⬝ᵥ y) :=
    fun Wt hWt y => pert W Wt α ε hα hWt y
  have hCt : ∀ Wt ∈ uncSet W ε, Coer Wt α := fun Wt hWt => ⟨_, hmd, fun y => by
    have h2 := hP Wt hWt y; have h3 := hQW y; rw [abs_le] at h2; nlinarith⟩
  have hκ : α * ℓ * ε / (1 - α * ℓ * (1 + ε)) = α * ε * ℓ / ((1 - α * ℓ) - α * ε * ℓ) := by
    ring_nf
  refine ⟨fun Wt hWt b hA2 => ?_, ?_, ?_⟩
  · -- part (a)
    obtain ⟨xs, hxs⟩ := solve W α hCW (fun i => (b i - c) / 2)
    obtain ⟨hopt, huniq, -, -⟩ := opt_struct W α b c hα hWnn hWsym hWd hCW hA2 xs hxs
    obtain ⟨xt, hxt⟩ := solve Wt α (hCt Wt hWt) (fun i => (b i - c) / 2)
    have hf : ∀ i, 0 < (b i - c) / 2 := fun i => by linarith [hA2 i]
    have hpos := pos_sol Wt α hα hWt.2.1 (hCt Wt hWt) _ xt (fun i => (hf i).le) hxt
    have heq : IsConsumptionEq Wt α b (fun i => b i - (b i - c) / 2) xt :=
      isEq_of_interior Wt α b _ xt hWt.2.2.2 (fun i => ((hf i).trans_le (hpos i)).le)
        (by rw [hxt]; ext i; simp only [Pi.sub_apply]; ring)
    refine ⟨⟨_, hopt⟩, fun p hp => ?_⟩
    rw [huniq p hp]
    exact ⟨xt, heq, fun i => (hf i).trans_le (hpos i)⟩
  · -- upper bound
    rintro r ⟨Wt, hWt, b, hA2, p, x, hp, hx, rfl⟩
    obtain ⟨xs, hxs⟩ := solve W α hCW (fun i => (b i - c) / 2)
    obtain ⟨-, huniq, hR, -⟩ := opt_struct W α b c hα hWnn hWsym hWd hCW hA2 xs hxs
    obtain ⟨xt, hxt⟩ := solve Wt α (hCt Wt hWt) (fun i => (b i - c) / 2)
    have hf : ∀ i, 0 < (b i - c) / 2 := fun i => by linarith [hA2 i]
    have hpos := pos_sol Wt α hα hWt.2.1 (hCt Wt hWt) _ xt (fun i => (hf i).le) hxt
    have heq : IsConsumptionEq Wt α b (fun i => b i - (b i - c) / 2) xt :=
      isEq_of_interior Wt α b _ xt hWt.2.2.2 (fun i => ((hf i).trans_le (hpos i)).le)
        (by rw [hxt]; ext i; simp only [Pi.sub_apply]; ring)
    have hpp := huniq p hp
    rw [hpp] at hx
    have hxx : x = xt := uniq Wt α b _ x xt hWt.2.2.2 (hCt Wt hWt) hx heq
    rw [hpp, hxx, hR, rev_ps, hκ]
    exact ratio_bound W Wt α (1 - α * ℓ) (α * ε * ℓ) hm hd hmd hWsym hWt.2.2.1 hQW
      (hP Wt hWt) _ xs xt hxs hxt
  · -- least
    intro u hu
    have hWW : W ∈ uncSet W ε := ⟨by simp only [sub_self, norm_zero]; positivity,
      hWnn, hWsym, hWd⟩
    by_cases hℓp : ℓ = 0
    · rw [hℓp]; simp only [mul_zero, zero_mul, zero_div]
      set b : Fin n → ℝ := fun _ => c + 2
      have hA2 : Assumption2 b c := fun i => by simp only [b]; linarith
      obtain ⟨xs, hxs⟩ := solve W α hCW (fun i => (b i - c) / 2)
      have hmem := mem_vol W W α c ε b hα hWnn hWsym hWd hCW hWW hCW hA2 xs xs hxs hxs
      refine le_trans ?_ (hu hmem)
      have : 0 ≤ xs ⬝ᵥ (fun i => (b i - c) / 2) := by rw [← hxs, ← Q_eq]; exact Q_nonneg hCW xs
      exact div_nonneg (abs_nonneg _) this
    · have hℓpos : 0 < ℓ := lt_of_le_of_ne hℓ0 (Ne.symm hℓp)
      obtain ⟨v, hv0, hvne, hWv⟩ := perron W hWnn hWsym hℓpos
      set Wt : Matrix (Fin n) (Fin n) ℝ := (1 + ε) • W with hWtdef
      have hWt : Wt ∈ uncSet W ε := by
        refine ⟨?_, fun i j => ?_, hWsym.smul (1 + ε), fun i => ?_⟩
        · have e : W - Wt = (-ε) • W := by
            rw [hWtdef, add_smul, one_smul, neg_smul]; abel
          rw [e, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hε]
        · simp only [Wt, Matrix.smul_apply, smul_eq_mul]
          exact mul_nonneg (by linarith) (hWnn i j)
        · simp only [Wt, Matrix.smul_apply, smul_eq_mul, hWd i, mul_zero]
      have hWtv : Wt *ᵥ v = ((1 + ε) * ℓ) • v := by
        rw [hWtdef, smul_mulVec, hWv, smul_smul]
      obtain ⟨u1, hu1⟩ := solve W α hCW (fun _ => 1)
      obtain ⟨u2, hu2⟩ := solve Wt α (hCt Wt hWt) (fun _ => 1)
      have hm' : 0 < 1 - α * ℓ * (1 + ε) := by linarith
      set s := 1 / (1 - α * ℓ) with hsdef
      set s' := 1 / (1 - α * ℓ * (1 + ε)) with hs'def
      have hs : s * (1 - α * ℓ) = 1 := by rw [hsdef]; field_simp
      have hs' : s' * (1 - α * ((1 + ε) * ℓ)) = 1 := by
        rw [hs'def, show α * ((1 + ε) * ℓ) = α * ℓ * (1 + ε) by ring]; field_simp
      set xsη : ℝ → Fin n → ℝ := fun η => s • v + η • u1
      set xtη : ℝ → Fin n → ℝ := fun η => s' • v + η • u2
      set fη : ℝ → Fin n → ℝ := fun η i => ((c + 2 * (v i + η)) - c) / 2
      have hxsη : ∀ η, xsη η - α • (W *ᵥ xsη η) = fη η := by
        intro η; ext i
        have := congrFun hu1 i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [xsη, fη, mulVec_add, mulVec_smul, hWv, Pi.sub_apply, Pi.smul_apply,
          Pi.add_apply, smul_eq_mul]
        linear_combination (v i) * hs + η * this
      have hxtη : ∀ η, xtη η - α • (Wt *ᵥ xtη η) = fη η := by
        intro η; ext i
        have := congrFun hu2 i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [xtη, fη, mulVec_add, mulVec_smul, hWtv, Pi.sub_apply, Pi.smul_apply,
          Pi.add_apply, smul_eq_mul]
        linear_combination (v i) * hs' + η * this
      set r : ℝ → ℝ := fun η =>
        |xsη η ⬝ᵥ fη η - xtη η ⬝ᵥ fη η| / (xsη η ⬝ᵥ fη η) with hrdef
      have hr_mem : ∀ η, 0 < η → r η ∈ volatilitySet W α c ε := by
        intro η hη
        have hA2 : Assumption2 (fun i => c + 2 * (v i + η)) c := fun i => by
          simp only; linarith [hv0 i]
        exact mem_vol W Wt α c ε (fun i => c + 2 * (v i + η)) hα hWnn hWsym hWd hCW hWt
          (hCt Wt hWt) hA2 (xsη η) (xtη η) (hxsη η) (hxtη η)
      have hF : Continuous fun η => xsη η ⬝ᵥ fη η :=
        Continuous.dotProduct (by fun_prop) (continuous_pi fun i => by fun_prop)
      have hG : Continuous fun η => xtη η ⬝ᵥ fη η :=
        Continuous.dotProduct (by fun_prop) (continuous_pi fun i => by fun_prop)
      have hvv : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dd_nonneg v)
        (fun h => hvne (dotProduct_self_eq_zero.mp h.symm))
      have hf0 : fη 0 = v := by ext i; simp only [fη]; ring
      have hF0 : xsη 0 ⬝ᵥ fη 0 = s * (v ⬝ᵥ v) := by
        rw [hf0]; simp only [xsη, zero_smul, add_zero, smul_dotProduct, smul_eq_mul]
      have hG0 : xtη 0 ⬝ᵥ fη 0 = s' * (v ⬝ᵥ v) := by
        rw [hf0]; simp only [xtη, zero_smul, add_zero, smul_dotProduct, smul_eq_mul]
      have hspos : 0 < s := by rw [hsdef]; positivity
      have hss : s ≤ s' := by
        rw [hsdef, hs'def]
        exact one_div_le_one_div_of_le hm' (by nlinarith [mul_nonneg hαℓ hε])
      have hr0 : r 0 = α * ℓ * ε / (1 - α * ℓ * (1 + ε)) := by
        simp only [hrdef]
        rw [hF0, hG0, abs_of_nonpos (by nlinarith), hsdef, hs'def]
        field_simp
        ring
      have hcont : ContinuousAt r 0 :=
        ((hF.sub hG).abs.continuousAt).div hF.continuousAt (by
          show xsη 0 ⬝ᵥ fη 0 ≠ 0
          rw [hF0]; positivity)
      rw [← hr0]
      refine le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))) ?_
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact hu (hr_mem η hη)
