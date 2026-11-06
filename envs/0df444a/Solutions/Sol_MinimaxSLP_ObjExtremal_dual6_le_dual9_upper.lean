-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.dual6_le_dual9_upper
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:04:00.377168+00:00
-- url     : https://prove2.me/submissions/35f1cf02-a2ac-46ef-95d0-8827a787d0fd

import Mathlib
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_Qval_homogeneous_superadditive
import Theorems.Thm_MinimaxSLP_ObjExtremal_scaled_weak_duality
import Theorems.Thm_LP_strong_duality_matrix

open MeasureTheory Matrix

namespace MSLP2SDP
open MinimaxSLP.ObjSDP MinimaxSLP.ObjExtremal

lemma bordered_quad {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (v0 : ℝ)
    (z : Fin d → ℝ) (c : ℝ) :
    star (Sum.elim z (fun _ : Fin 1 => c)) ⬝ᵥ (bordered V v v0 *ᵥ Sum.elim z (fun _ => c)) =
      z ⬝ᵥ (V *ᵥ z) + 2 * c * (z ⬝ᵥ v) + c ^ 2 * v0 := by
  simp only [star_trivial, bordered, dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, of_apply,
    Fin.sum_univ_one]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have : ∀ i, ∑ j, z i * (V i j * z j) = ∑ j, z i * V i j * z j := fun i =>
    Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => this i]
  have e1 : ∑ i, z i * (v i * c) = ∑ i, c * (z i * v i) := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, c * (v i * z i) = ∑ i, c * (z i * v i) := Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  simp only [← Finset.mul_sum]
  ring

open scoped MatrixOrder in
lemma psd_factor {ι : Type} [Fintype ι] [DecidableEq ι] (R : Matrix ι ι ℝ) (hR : R.PosSemidef) :
    ∃ B : Matrix ι ι ℝ, R = Bᵀ * B := by
  have h0 : 0 ≤ R := hR.nonneg
  refine ⟨CFC.sqrt R, ?_⟩
  have hs := (CFC.sqrt_nonneg R).posSemidef.1
  have : (CFC.sqrt R)ᵀ = CFC.sqrt R := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hs
  rw [this, CFC.sqrt_mul_sqrt_self R h0]

lemma bordered_psd_iff {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (v0 : ℝ) :
    (bordered V v v0).PosSemidef ↔
      V.IsSymm ∧ ∀ z c, 0 ≤ z ⬝ᵥ (V *ᵥ z) + 2 * c * (z ⬝ᵥ v) + c ^ 2 * v0 := by
  constructor
  · intro hP
    refine ⟨?_, fun z c => ?_⟩
    · ext a b
      have := congrFun (congrFun hP.1 (Sum.inl a)) (Sum.inl b)
      simpa [bordered, conjTranspose_apply, transpose_apply] using this
    · rw [← bordered_quad]; exact hP.dotProduct_mulVec_nonneg _
  · rintro ⟨hS, hq⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext a b
      rcases a with a | a <;> rcases b with b | b
      · simpa [bordered, conjTranspose_apply] using congrFun (congrFun hS a) b
      · simp [bordered, conjTranspose_apply]
      · simp [bordered, conjTranspose_apply]
      · simp [bordered, conjTranspose_apply]
    · intro y
      have hy : y = Sum.elim (fun a => y (Sum.inl a)) (fun _ : Fin 1 => y (Sum.inr 0)) := by
        funext a; rcases a with a | a
        · rfl
        · simp [Fin.fin_one_eq_zero a]
      rw [hy, bordered_quad]
      exact hq _ _

/-- LP attainment: `𝒬(q, x)` is the attained maximum of its dual. -/
lemma Qval_dual_attained {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) (q : Fin d → ℝ) :
    ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q ∧ (h - T *ᵥ x) ⬝ᵥ π = Qval W T h q x := by
  obtain ⟨w0, hw01, hw02⟩ := hrec
  obtain ⟨π, y, hπ, hy0, hy, hval, -⟩ := LP.strong_duality_matrix Wᵀ q (h - T *ᵥ x) (hA3 q)
    ⟨w0, hw02, by rw [transpose_transpose, hw01]⟩
  refine ⟨π, hπ, le_antisymm ?_ ?_⟩
  · have := scaled_weak_duality W T h hA3 x ⟨w0, hw01, hw02⟩ 1 zero_le_one q π (by simpa using hπ)
    simpa using this
  · rw [hval]
    apply csInf_le
    · refine ⟨(h - T *ᵥ x) ⬝ᵥ π, ?_⟩
      rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
      have e1 : (h - T *ᵥ x) ⬝ᵥ π = (Wᵀ *ᵥ π) ⬝ᵥ w := by
        rw [← hw1, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      rw [e1]
      exact dotProduct_le_dotProduct_of_nonneg_right hπ hw2
    · refine ⟨y, ⟨?_, hy0⟩, rfl⟩
      rw [transpose_transpose] at hy
      exact hy

/-- linear lower bound for `𝒬(·, x)` -/
lemma Qval_lower {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    ∃ C : Fin d → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ ρ, -(∑ i, |ρ i| * C i) ≤ Qval W T h ρ x := by
  obtain ⟨hhom, hsup⟩ := Qval_homogeneous_superadditive W T h hA3 x hrec
  set Qv : (Fin d → ℝ) → ℝ := fun q => Qval W T h q x with hQv
  have hQv0 : Qv 0 = 0 := by
    have := hhom 2 (by norm_num) 0
    simp only [smul_zero] at this
    show Qval W T h 0 x = 0
    linarith
  have hsupsum : ∀ (s : Finset (Fin d)) (f : Fin d → Fin d → ℝ),
      ∑ i ∈ s, Qv (f i) ≤ Qv (∑ i ∈ s, f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hQv0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have : Qv (f a) + Qv (∑ i ∈ s, f i) ≤ Qv (f a + ∑ i ∈ s, f i) := hsup _ _
      linarith
  set e : Fin d → Fin d → ℝ := fun i => Pi.single i 1 with he
  have hscal : ∀ (t : ℝ) (u : Fin d → ℝ), -(|t| * (|Qv u| + |Qv (-u)|)) ≤ Qv (t • u) := by
    intro t u
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have : t • u = (-t) • (-u) := by rw [neg_smul_neg]
      rw [this]
      show _ ≤ Qval W T h ((-t) • -u) x
      rw [hhom (-t) (by linarith)]
      rw [abs_of_neg ht]
      have := neg_abs_le (Qv (-u))
      have := abs_nonneg (Qv u)
      show _ ≤ -t * Qv (-u)
      nlinarith
    · subst ht; simp [hQv0]
    · show _ ≤ Qval W T h (t • u) x
      rw [hhom t ht, abs_of_pos ht]
      have := neg_abs_le (Qv u)
      have := abs_nonneg (Qv (-u))
      show _ ≤ t * Qv u
      nlinarith
  refine ⟨fun i => |Qv (e i)| + |Qv (-e i)|, fun i => by positivity, fun ρ => ?_⟩
  have hρ : ρ = ∑ i, ρ i • e i := by
    rw [he]; exact pi_eq_sum_univ' ρ
  have h1 := hsupsum Finset.univ (fun i => ρ i • e i)
  rw [← hρ] at h1
  refine le_trans ?_ h1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun i _ => hscal (ρ i) (e i)


lemma bordered_add {d : ℕ} (V V' : Matrix (Fin d) (Fin d) ℝ) (v v' : Fin d → ℝ) (c c' : ℝ) :
    bordered (V + V') (v + v') (c + c') = bordered V v c + bordered V' v' c' := by
  ext (i | i) (j | j) <;> simp [bordered]

lemma bordered_smul {d : ℕ} (θ : ℝ) (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (c : ℝ) :
    bordered (θ • V) (θ • v) (θ * c) = θ • bordered V v c := by
  ext (i | i) (j | j) <;> simp [bordered]

lemma bordered_zero {d : ℕ} : bordered (0 : Matrix (Fin d) (Fin d) ℝ) 0 0 = 0 := by
  ext (i | i) (j | j) <;> simp [bordered]

/-- the convex cone of (moment matrix, value) pairs generated by relaxed feasible points of (9) -/
def coneC {n r d K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (x : Fin n → ℝ) :
    Set (((Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ) × ℝ) :=
  {z | ∃ s : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ),
    (∀ k, (bordered (s.1 k) (s.2.1 k) (s.2.2.1 k)).PosSemidef) ∧
    (∀ k, Wᵀ *ᵥ s.2.2.2 k ≤ α k • s.2.1 k) ∧
    ∃ N : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ, (∀ a b, N a b = -N b a) ∧
      (∀ a b, z.1 a b = (∑ k, bordered (s.1 k) (s.2.1 k) (s.2.2.1 k)) a b + N a b) ∧
      z.2 ≤ obj9 T h β x s}

lemma coneC_add {n r d K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (x : Fin n → ℝ) {z z' : _}
    (hz : z ∈ coneC W T h α β x) (hz' : z' ∈ coneC W T h α β x) :
    z + z' ∈ coneC W T h α β x := by
  obtain ⟨s, hp, hd, N, hN, he, hv⟩ := hz
  obtain ⟨s', hp', hd', N', hN', he', hv'⟩ := hz'
  refine ⟨s + s', fun k => ?_, fun k => ?_, N + N', fun a b => ?_, fun a b => ?_, ?_⟩
  · have := (hp k).add (hp' k)
    simpa [← bordered_add] using this
  · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mulVec_add, smul_add]
    exact add_le_add (hd k) (hd' k)
  · simp only [Pi.add_apply, hN a b, hN' a b]; ring
  · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, bordered_add, Finset.sum_add_distrib,
      Matrix.add_apply, he a b, he' a b]
    ring
  · simp only [Prod.snd_add, obj9, Prod.fst_add, Pi.add_apply, dotProduct_add] at hv hv' ⊢
    rw [show ∑ k, ((h - T *ᵥ x) ⬝ᵥ s.2.2.2 k + (h - T *ᵥ x) ⬝ᵥ s'.2.2.2 k +
        β k * (s.2.2.1 k + s'.2.2.1 k)) =
        ∑ k, ((h - T *ᵥ x) ⬝ᵥ s.2.2.2 k + β k * s.2.2.1 k) +
        ∑ k, ((h - T *ᵥ x) ⬝ᵥ s'.2.2.2 k + β k * s'.2.2.1 k) by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring]
    linarith

lemma coneC_smul {n r d K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (x : Fin n → ℝ) {z : _}
    (hz : z ∈ coneC W T h α β x) {θ : ℝ} (hθ : 0 ≤ θ) :
    θ • z ∈ coneC W T h α β x := by
  obtain ⟨s, hp, hd, N, hN, he, hv⟩ := hz
  refine ⟨θ • s, fun k => ?_, fun k => ?_, θ • N, fun a b => ?_, fun a b => ?_, ?_⟩
  · have := (hp k).smul hθ
    simpa [← bordered_smul] using this
  · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, mulVec_smul]
    rw [smul_comm (α k) θ]
    exact smul_le_smul_of_nonneg_left (hd k) hθ
  · simp only [Pi.smul_apply, smul_eq_mul, hN a b]; ring
  · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, bordered_smul,
      ← Finset.smul_sum, Matrix.smul_apply, he a b]
    ring
  · simp only [Prod.smul_snd, obj9, Prod.smul_fst, Pi.smul_apply, dotProduct_smul,
      smul_eq_mul] at hv ⊢
    rw [show ∑ k, (θ * ((h - T *ᵥ x) ⬝ᵥ s.2.2.2 k) + β k * (θ * s.2.2.1 k)) =
        θ * ∑ k, ((h - T *ᵥ x) ⬝ᵥ s.2.2.2 k + β k * s.2.2.1 k) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring]
    exact mul_le_mul_of_nonneg_left hv hθ

lemma coneC_convex {n r d K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (x : Fin n → ℝ) :
    Convex ℝ (coneC W T h α β x) := by
  intro z hz z' hz' a b ha hb _
  exact coneC_add W T h α β x (coneC_smul W T h α β x hz ha) (coneC_smul W T h α β x hz' hb)

/-- a single block (index `k0`) gives a point of the cone -/
lemma single_mem {n r d K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) (k0 : Fin K)
    (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (v0 : ℝ) (hpsd : (bordered V v v0).PosSemidef)
    (N : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ) (hN : ∀ a b, N a b = -N b a)
    (t : ℝ) (ht : t ≤ α k0 * Qval W T h v x + β k0 * v0) :
    ((fun a b => bordered V v v0 a b + N a b), t) ∈ coneC W T h α β x := by
  classical
  obtain ⟨π, hπ, hπv⟩ := Qval_dual_attained W T h hA3 x hrec v
  refine ⟨(fun k => if k = k0 then V else 0, fun k => if k = k0 then v else 0,
    fun k => if k = k0 then v0 else 0, fun k => if k = k0 then α k0 • π else 0),
    fun k => ?_, fun k => ?_, N, hN, fun a b => ?_, ?_⟩
  · by_cases hk : k = k0
    · simp only [hk, if_true]; exact hpsd
    · simp only [hk, if_false, bordered_zero]; exact PosSemidef.zero
  · by_cases hk : k = k0
    · subst hk; simp only [if_true, mulVec_smul]
      exact smul_le_smul_of_nonneg_left hπ (hα k)
    · simp [hk]
  · simp only
    congr 1
    rw [Matrix.sum_apply, Fintype.sum_eq_single k0]
    · simp
    · intro k hk; simp [hk, bordered_zero]
  · simp only [obj9]
    rw [Fintype.sum_eq_single k0]
    · simp only [if_true, dotProduct_smul, smul_eq_mul, hπv]; linarith
    · intro k hk; simp [hk]


lemma Qval_zero {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) : Qval W T h 0 x = 0 := by
  have := (Qval_homogeneous_superadditive W T h hA3 x hrec).1 2 (by norm_num) 0
  simp only [smul_zero] at this
  linarith

lemma rank1_mem {n r d K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) (k0 : Fin K)
    (q : Fin d → ℝ) (c : ℝ) :
    ((fun a b => Sum.elim q (fun _ : Fin 1 => c) a * Sum.elim q (fun _ : Fin 1 => c) b),
      α k0 * Qval W T h (c • q) x + β k0 * c ^ 2) ∈ coneC W T h α β x := by
  have hpsd : (bordered (vecMulVec q q) (c • q) (c ^ 2)).PosSemidef := by
    rw [bordered_psd_iff]
    refine ⟨?_, fun z t => ?_⟩
    · ext a b; simp [vecMulVec_apply, mul_comm]
    · have e1 : z ⬝ᵥ (vecMulVec q q *ᵥ z) = (z ⬝ᵥ q) ^ 2 := by
        rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm q z]
        ring
      rw [e1, dotProduct_smul, smul_eq_mul]
      nlinarith [sq_nonneg (z ⬝ᵥ q + t * c)]
  have := single_mem W T h α β hα hA3 x hrec k0 _ _ _ hpsd 0 (fun _ _ => by simp) _ le_rfl
  convert this using 2
  funext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [bordered, vecMulVec_apply] <;> ring

lemma ball_sub {n r d K : ℕ} [NeZero K] (W : Matrix (Fin r) (Fin d) ℝ)
    (T : Matrix (Fin r) (Fin n) ℝ)
    (h : Fin r → ℝ) (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    ∃ z1 ρ, 0 < ρ ∧ Metric.ball z1 ρ ⊆ coneC W T h α β x := by
  classical
  obtain ⟨C, hC0, hClow⟩ := Qval_lower W T h hA3 x hrec
  set k0 : Fin K := 0
  set t1 : ℝ := -(α k0 * ∑ i, C i) - 2 * |β k0| - 1 with ht1
  have hn : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  set ρ : ℝ := 1 / ((d : ℝ) + 1) with hρ
  have hρpos : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hn]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  refine ⟨(fun a b => if a = b then 1 else 0, t1), ρ, hρpos, fun z hz => ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hz
  obtain ⟨hz1, hz2⟩ := hz
  have hE : ∀ a b, |z.1 a b - (if a = b then 1 else 0)| < ρ := by
    intro a b
    have := (dist_le_pi_dist (z.1 a) (fun b => if a = b then (1 : ℝ) else 0) b).trans
      (dist_le_pi_dist z.1 (fun a b => if a = b then (1 : ℝ) else 0) a)
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt this hz1
  rw [Real.dist_eq] at hz2
  set M := z.1 with hM
  set Sm : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ := fun a b => (M a b + M b a) / 2 with hSm
  set N : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ := fun a b => (M a b - M b a) / 2 with hN
  set V : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun a b => Sm (Sum.inl a) (Sum.inl b)
  set v : Fin d → ℝ := fun a => Sm (Sum.inl a) (Sum.inr 0)
  set v0 : ℝ := Sm (Sum.inr 0) (Sum.inr 0)
  have hB : ∀ a b, bordered V v v0 a b = Sm a b := by
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · simp [bordered, V]
    · simp [bordered, v, Fin.fin_one_eq_zero b]
    · simp only [bordered, fromBlocks_apply₂₁, of_apply, v, Fin.fin_one_eq_zero a, hSm]; ring
    · simp [bordered, v0, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
  have hSE : ∀ a b, |Sm a b - (if a = b then 1 else 0)| < ρ := by
    intro a b
    have h1 := hE a b
    have h2 := hE b a
    have e : (if b = a then (1 : ℝ) else 0) = if a = b then 1 else 0 := by
      by_cases hab : a = b <;> simp [hab, eq_comm]
    rw [e] at h2
    rw [abs_lt] at h1 h2 ⊢
    simp only [hSm]
    constructor <;> linarith
  have hpsd : (bordered V v v0).PosSemidef := by
    have heq : bordered V v v0 = Matrix.of Sm := by ext a b; exact hB a b
    rw [heq]
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext a b; simp only [conjTranspose_apply, star_trivial, of_apply, hSm]; ring
    · intro y
      simp only [star_trivial, dotProduct, mulVec, of_apply, Finset.mul_sum]
      have key : ∀ a b, y a * (Sm a b * y b) ≥
          y a * ((if a = b then 1 else 0) * y b) - ρ * (|y a| * |y b|) := by
        intro a b
        have := hSE a b
        have h3 : |y a * ((Sm a b - (if a = b then 1 else 0)) * y b)| ≤ ρ * (|y a| * |y b|) := by
          rw [abs_mul, abs_mul]
          have := abs_nonneg (y a); have := abs_nonneg (y b)
          nlinarith [mul_nonneg (abs_nonneg (y a)) (abs_nonneg (y b))]
        have h4 := neg_abs_le (y a * ((Sm a b - (if a = b then 1 else 0)) * y b))
        nlinarith
      have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
        Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => key a b
      have hdiag : ∀ a, ∑ b, (y a * ((if a = b then (1 : ℝ) else 0) * y b) -
          ρ * (|y a| * |y b|)) = y a ^ 2 - ρ * ∑ b, |y a| * |y b| := by
        intro a; rw [Finset.sum_sub_distrib, Finset.mul_sum]; congr 1; simp [sq]
      rw [Finset.sum_congr rfl fun a _ => hdiag a, Finset.sum_sub_distrib] at hsum
      have hcs : (∑ a, |y a|) ^ 2 ≤ (Finset.univ : Finset (Fin d ⊕ Fin 1)).card *
          ∑ a, |y a| ^ 2 := sq_sum_le_card_mul_sum_sq
      have hcard : ((Finset.univ : Finset (Fin d ⊕ Fin 1)).card : ℝ) = (d : ℝ) + 1 := by
        simp
      rw [hcard] at hcs
      simp only [sq_abs] at hcs
      have hexp : ∑ a, ρ * ∑ b, |y a| * |y b| = ρ * (∑ a, |y a|) ^ 2 := by
        rw [← Finset.mul_sum, sq, Finset.sum_mul_sum]
      rw [hexp] at hsum
      have : ρ * (∑ a, |y a|) ^ 2 ≤ ∑ a, y a ^ 2 := by
        calc ρ * (∑ a, |y a|) ^ 2 ≤ ρ * (((d : ℝ) + 1) * ∑ a, y a ^ 2) :=
              mul_le_mul_of_nonneg_left hcs hρpos.le
          _ = ∑ a, y a ^ 2 := by rw [hρ]; field_simp
      linarith
  have hNanti : ∀ a b, N a b = -N b a := fun a b => by simp only [hN]; ring
  -- value bound
  have hv : ∀ a, |v a| ≤ 1 := by
    intro a
    have := hSE (Sum.inl a) (Sum.inr 0)
    simp only [reduceCtorEq, if_false, sub_zero] at this
    exact this.le.trans hρ1
  have hv0 : |v0| ≤ 2 := by
    have := hSE (Sum.inr 0) (Sum.inr 0)
    simp only [if_true] at this
    rw [abs_lt] at this
    rw [abs_le]; constructor <;> linarith
  have hQl := hClow v
  have hQl' : -(∑ i, C i) ≤ Qval W T h v x := by
    refine le_trans ?_ hQl
    rw [neg_le_neg_iff]
    exact Finset.sum_le_sum fun i _ => by
      have := hv i; have := hC0 i; nlinarith [abs_nonneg (v i)]
  have hbeta : -(2 * |β k0|) ≤ β k0 * v0 := by
    have := neg_abs_le (β k0 * v0)
    rw [abs_mul] at this
    nlinarith [abs_nonneg (β k0), abs_nonneg v0]
  have ht : z.2 ≤ α k0 * Qval W T h v x + β k0 * v0 := by
    have h1 : α k0 * -(∑ i, C i) ≤ α k0 * Qval W T h v x := mul_le_mul_of_nonneg_left hQl' (hα k0)
    rw [abs_lt] at hz2
    nlinarith
  have := single_mem W T h α β hα hA3 x hrec k0 V v v0 hpsd N hNanti z.2 ht
  convert this using 1
  refine Prod.ext ?_ rfl
  funext a b
  show z.1 a b = bordered V v v0 a b + N a b
  rw [hB a b]
  simp only [hSm, hN, hM]
  ring


lemma Mbar_posDef {d : ℕ} (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm)
    (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef) : (bordered Q μ 1).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [bordered, conjTranspose_apply, Fin.fin_one_eq_zero]
    exact congrFun (congrFun hQ a) b
  · intro y hy
    have hy' : y = Sum.elim (fun a => y (Sum.inl a)) (fun _ : Fin 1 => y (Sum.inr 0)) := by
      funext a; rcases a with a | a
      · rfl
      · simp [Fin.fin_one_eq_zero a]
    rw [hy', bordered_quad]
    set z : Fin d → ℝ := fun a => y (Sum.inl a)
    set c := y (Sum.inr 0)
    have e : z ⬝ᵥ (Q *ᵥ z) = z ⬝ᵥ ((Q - vecMulVec μ μ) *ᵥ z) + (z ⬝ᵥ μ) ^ 2 := by
      rw [sub_mulVec, dotProduct_sub, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul,
        smul_eq_mul, dotProduct_comm μ z]
      ring
    rw [e]
    by_cases hz : z = 0
    · have hc : c ≠ 0 := by
        intro hc; apply hy; rw [hy']; funext a; rcases a with a | a
        · simp only [Sum.elim_inl]; exact congrFun hz a
        · simp [hc]
      rw [hz]; simp; positivity
    · have := hA4.dotProduct_mulVec_pos hz
      simp only [star_trivial] at this
      nlinarith [sq_nonneg (z ⬝ᵥ μ + c)]

/-- the Frobenius-type pairing of two function-matrices -/
def pair {ι : Type} [Fintype ι] (G M : ι → ι → ℝ) : ℝ := ∑ a, ∑ b, M a b * G a b

theorem sdp_main {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (u : ℝ) (hu : u ∈ upperBounds (dualValues9 W T h α β μ Q x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ s ∈ dualFeasible6 W T h α β x, frob Q s.1 + μ ⬝ᵥ s.2.1 + s.2.2 ≤ u + ε := by
  classical
  set Cn := coneC W T h α β x with hCn
  set Mb : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ := fun a b => bordered Q μ 1 a b with hMb
  set z0 : ((Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ) × ℝ := (Mb, u + ε) with hz0
  -- z0 is not in the cone
  have hz0C : z0 ∉ Cn := by
    rintro ⟨s, hp, hd, N, hN, he, hv⟩
    have hsymB : ∀ a b, (∑ k, bordered (s.1 k) (s.2.1 k) (s.2.2.1 k)) a b =
        (∑ k, bordered (s.1 k) (s.2.1 k) (s.2.2.1 k)) b a := by
      intro a b
      simp only [Matrix.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := congrFun (congrFun (hp k).1 a) b
      simpa [conjTranspose_apply] using this.symm
    have hsymM : ∀ a b, Mb a b = Mb b a := by
      intro a b
      rcases a with a | a <;> rcases b with b | b <;>
        simp [hMb, bordered, Fin.fin_one_eq_zero]
      exact congrFun (congrFun hQ b) a
    have hN0 : ∀ a b, N a b = 0 := by
      intro a b
      have h1 := he a b
      have h2 := he b a
      have h3 := hN a b
      simp only [hz0] at h1 h2
      have h4 := hsymM a b
      have h5 := hsymB a b
      linarith
    have hfeas : s ∈ feasible9 W α μ Q := by
      refine ⟨?_, hp, hd⟩
      ext a b
      have := he a b
      simp only [hz0, hN0, add_zero] at this
      exact this.symm
    have := hu ⟨s, hfeas, rfl⟩
    simp only [hz0] at hv
    linarith
  have hconv : Convex ℝ Cn := coneC_convex W T h α β x
  obtain ⟨z1, ρ, hρ, hball⟩ := ball_sub W T h α β hα hA3 x hrec
  have hint : (interior Cn).Nonempty :=
    ⟨z1, interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hρ)⟩
  obtain ⟨f, hf0, hf⟩ := geometric_hahn_banach_of_nonempty_interior_point hconv
    (fun hmem => hz0C (interior_subset hmem)) hint
  -- f is nonpositive on the cone
  have hfC : ∀ c ∈ Cn, f c ≤ 0 := by
    intro c hc
    by_contra hpos
    push_neg at hpos
    set θ := (|f z0| + 1) / f c
    have hθ : 0 < θ := by positivity
    have := hf _ (coneC_smul W T h α β x hc hθ.le)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    linarith [le_abs_self (f z0)]
  have h0C : ((0 : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ), (0 : ℝ)) ∈ Cn := by
    have := single_mem W T h α β hα hA3 x hrec 0 0 0 0 (by rw [bordered_zero]; exact PosSemidef.zero)
      0 (fun _ _ => by simp) 0 (by simp [Qval_zero W T h hA3 x hrec])
    convert this using 2
    funext a b; simp [bordered_zero]
  have hfz0 : 0 ≤ f z0 := by
    have := hf _ h0C
    rw [show ((0 : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ), (0 : ℝ)) = 0 from rfl, map_zero] at this
    exact this
  -- coordinates of f
  set E : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ((Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ) := fun a b i j => if i = a ∧ j = b then 1 else 0 with hE
  set G : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ := fun a b => f (E a b, 0) with hG
  set lam : ℝ := f (0, 1) with hlam
  have hdec : ∀ M : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ, M = ∑ a, ∑ b, M a b • E a b := by
    intro M
    funext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hE, mul_ite, mul_one, mul_zero,
      ite_and]
    simp
  have hrep : ∀ z : ((Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ) × ℝ, f z = pair G z.1 + z.2 * lam := by
    intro z
    have hz : z = (z.1, 0) + z.2 • ((0 : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ), (1 : ℝ)) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [hz, map_add, map_smul, smul_eq_mul]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero, add_zero,
      smul_eq_mul, mul_one, zero_add]
    congr 1
    · have hL : f (z.1, 0) = (f.comp (ContinuousLinearMap.inl ℝ _ ℝ))
          (∑ a, ∑ b, z.1 a b • E a b) := by
        conv_lhs => rw [hdec z.1]
        rfl
      rw [hL, map_sum]
      simp only [map_sum, map_smul, smul_eq_mul, pair, hG]
      rfl
  -- symmetry of G
  have hGsym : ∀ a b, G a b = G b a := by
    intro a b
    set Nn : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ := E a b - E b a
    have hNn : ∀ i j, Nn i j = -Nn j i := by
      intro i j
      simp only [Nn, hE, Pi.sub_apply]
      by_cases h1 : i = a <;> by_cases h2 : j = b <;> by_cases h3 : i = b <;>
        by_cases h4 : j = a <;> simp [h1, h2, h3, h4, and_comm]
    have mem : ∀ (N : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ), (∀ i j, N i j = -N j i) → (N, (0 : ℝ)) ∈ Cn := by
      intro N hN
      have := single_mem W T h α β hα hA3 x hrec 0 0 0 0
        (by rw [bordered_zero]; exact PosSemidef.zero) N hN 0
        (by simp [Qval_zero W T h hA3 x hrec])
      convert this using 2
      funext i j; simp [bordered_zero]
    have h1 := hfC _ (mem Nn hNn)
    have h2 := hfC _ (mem (-Nn) (fun i j => by simp only [Pi.neg_apply, hNn i j, neg_neg]))
    have e1 : f (Nn, 0) = G a b - G b a := by
      rw [show (Nn, (0 : ℝ)) = (E a b, (0 : ℝ)) - (E b a, 0) by simp [Nn], map_sub]
    have e2 : f (-Nn, 0) = -(G a b - G b a) := by
      rw [show (-Nn, (0 : ℝ)) = -(Nn, (0 : ℝ)) by simp, map_neg, e1]
    linarith
  -- the rank-one points
  have hrank : ∀ k (q : Fin d → ℝ) (c : ℝ),
      pair G (fun a b => Sum.elim q (fun _ : Fin 1 => c) a * Sum.elim q (fun _ : Fin 1 => c) b) +
        (α k * Qval W T h (c • q) x + β k * c ^ 2) * lam ≤ 0 := by
    intro k q c
    have := hfC _ (rank1_mem W T h α β hα hA3 x hrec k q c)
    rwa [hrep] at this
  -- lam ≥ 0
  have hlam0 : 0 ≤ lam := by
    have := single_mem W T h α β hα hA3 x hrec 0 0 0 0
      (by rw [bordered_zero]; exact PosSemidef.zero) 0 (fun _ _ => by simp) (-1)
      (by simp [Qval_zero W T h hA3 x hrec])
    have := hfC _ this
    rw [hrep] at this
    simp [pair, bordered_zero] at this
    linarith
  -- lam ≠ 0
  have hlampos : 0 < lam := by
    rcases hlam0.lt_or_eq with hl | hl
    · exact hl
    exfalso
    have hl' : lam = 0 := hl.symm
    -- `-G` is positive semidefinite
    have hA : (Matrix.of fun a b => -G a b).PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
      · ext a b; simp [conjTranspose_apply, hGsym b a]
      · intro w
        have hw : w = Sum.elim (fun a => w (Sum.inl a)) (fun _ : Fin 1 => w (Sum.inr 0)) := by
          funext a; rcases a with a | a
          · rfl
          · simp [Fin.fin_one_eq_zero a]
        have := hrank 0 (fun a => w (Sum.inl a)) (w (Sum.inr 0))
        rw [hl', mul_zero, add_zero, ← hw] at this
        simp only [star_trivial, dotProduct, mulVec, of_apply, Finset.mul_sum]
        simp only [pair] at this
        have e : ∑ a, ∑ b, w a * (-G a b * w b) = -∑ a, ∑ b, w a * w b * G a b := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [e]; linarith
    obtain ⟨B, hBf⟩ := psd_factor _ hA
    have hMpd := Mbar_posDef μ Q hQ hA4
    have hBG : ∀ a b, -G a b = ∑ i, B i a * B i b := by
      intro a b
      have := congrFun (congrFun hBf a) b
      simpa [Matrix.mul_apply, transpose_apply] using this
    have hsum : ∑ i, (fun a => B i a) ⬝ᵥ (bordered Q μ 1 *ᵥ fun a => B i a) =
        -pair G Mb := by
      have lhs : ∑ i, (fun a => B i a) ⬝ᵥ (bordered Q μ 1 *ᵥ fun a => B i a) =
          ∑ i, ∑ a, ∑ b, B i a * Mb a b * B i b := by
        simp only [dotProduct, mulVec, Finset.mul_sum, hMb]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => by ring
      have rhs : -pair G Mb = ∑ a, ∑ b, ∑ i, B i a * Mb a b * B i b := by
        simp only [pair, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [← mul_neg, hBG a b, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [lhs, rhs, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
    have hpz : pair G Mb ≥ 0 := by
      have := hrep z0; rw [hl', mul_zero, add_zero] at this
      rw [← this]; exact hfz0
    have hnn : ∀ i, 0 ≤ (fun a => B i a) ⬝ᵥ (bordered Q μ 1 *ᵥ fun a => B i a) := by
      intro i; simpa using hMpd.posSemidef.dotProduct_mulVec_nonneg (fun a => B i a)
    have hzero : ∀ i, (fun a => B i a) ⬝ᵥ (bordered Q μ 1 *ᵥ fun a => B i a) = 0 := by
      have := Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hnn i)
      have h2 : ∑ i, (fun a => B i a) ⬝ᵥ (bordered Q μ 1 *ᵥ fun a => B i a) = 0 :=
        le_antisymm (by rw [hsum]; linarith) (Finset.sum_nonneg fun i _ => hnn i)
      exact fun i => (this.mp h2) i (Finset.mem_univ i)
    have hB0 : B = 0 := by
      ext i a
      by_contra hne
      have hrow : (fun a => B i a) ≠ 0 := fun h0 => hne (congrFun h0 a)
      have := hMpd.dotProduct_mulVec_pos hrow
      simp only [star_trivial] at this
      linarith [hzero i]
    have hG0 : ∀ a b, G a b = 0 := by
      intro a b
      have := congrFun (congrFun hBf a) b
      simp [hB0] at this
      linarith
    apply hf0
    refine ContinuousLinearMap.ext fun z => ?_
    rw [hrep, hl']
    simp [pair, hG0]
  -- the dual point
  set Y : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun a b => -G (Sum.inl a) (Sum.inl b) / lam
  set y : Fin d → ℝ := fun a => -(2 * G (Sum.inl a) (Sum.inr 0)) / lam
  set y0 : ℝ := -G (Sum.inr 0) (Sum.inr 0) / lam
  have hexp : ∀ (q : Fin d → ℝ), pair G (fun a b => Sum.elim q (fun _ : Fin 1 => (1 : ℝ)) a *
      Sum.elim q (fun _ : Fin 1 => (1 : ℝ)) b) = -lam * (q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y0) := by
    intro q
    simp only [pair, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one,
      one_mul, mul_one, dotProduct, mulVec, Y, y, y0, of_apply]
    have hl0 : lam ≠ 0 := hlampos.ne'
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    rw [show ∑ i, q i * G (Sum.inr 0) (Sum.inl i) = ∑ i, q i * G (Sum.inl i) (Sum.inr 0) from
      Finset.sum_congr rfl fun i _ => by rw [hGsym (Sum.inr 0) (Sum.inl i)]]
    have e1 : ∀ i j, -lam * (q i * (-G (Sum.inl i) (Sum.inl j) / lam * q j)) =
        q i * q j * G (Sum.inl i) (Sum.inl j) := fun i j => by field_simp
    have e2 : ∀ i, -lam * (q i * (-(2 * G (Sum.inl i) (Sum.inr 0)) / lam)) =
        2 * (q i * G (Sum.inl i) (Sum.inr 0)) := fun i => by field_simp
    simp only [e1, e2, ← Finset.mul_sum]
    field_simp
    ring
  refine ⟨(Y, y, y0), ⟨?_, fun q => ?_⟩, ?_⟩
  · ext a b; simp only [Y, transpose_apply, of_apply]; rw [hGsym]
  · simp only
    apply Finset.sup'_le
    intro k _
    have := hrank k q 1
    rw [hexp q, one_smul, one_pow, mul_one] at this
    have : lam * (α k * Qval W T h q x + β k) ≤ lam * (q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y0) := by
      linarith
    exact le_of_mul_le_mul_left this hlampos
  · simp only
    have hz := hrep z0
    have hpairM : pair G Mb = -lam * (frob Q Y + μ ⬝ᵥ y + y0) := by
      simp only [pair, hMb, Fintype.sum_sum_type, bordered, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Fin.sum_univ_one,
        one_mul, frob, dotProduct, Y, y, y0]
      have hl0 : lam ≠ 0 := hlampos.ne'
      rw [show ∑ i, μ i * G (Sum.inr 0) (Sum.inl i) = ∑ i, μ i * G (Sum.inl i) (Sum.inr 0) from
        Finset.sum_congr rfl fun i _ => by rw [hGsym (Sum.inr 0) (Sum.inl i)]]
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
      have e1 : ∀ i j, -lam * (Q i j * (-G (Sum.inl i) (Sum.inl j) / lam)) =
          Q i j * G (Sum.inl i) (Sum.inl j) := fun i j => by field_simp
      have e2 : ∀ i, -lam * (μ i * (-(2 * G (Sum.inl i) (Sum.inr 0)) / lam)) =
          2 * (μ i * G (Sum.inl i) (Sum.inr 0)) := fun i => by field_simp
      simp only [e1, e2, ← Finset.mul_sum]
      field_simp
      ring
    rw [hpairM] at hz
    simp only [hz0] at hz
    have : 0 ≤ -lam * (frob Q Y + μ ⬝ᵥ y + y0) + (u + ε) * lam := by rw [← hz]; exact hfz0
    have : lam * (frob Q Y + μ ⬝ᵥ y + y0) ≤ lam * (u + ε) := by linarith
    exact le_of_mul_le_mul_left this hlampos

end MSLP2SDP

open MinimaxSLP.ObjExtremal in
theorem solution {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (u : ℝ) (hu : u ∈ upperBounds (dualValues9 W T h α β μ Q x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ s ∈ MinimaxSLP.ObjSDP.dualFeasible6 W T h α β x,
      MinimaxSLP.ObjSDP.frob Q s.1 + μ ⬝ᵥ s.2.1 + s.2.2 ≤ u + ε :=
  MSLP2SDP.sdp_main W T h α β hα μ Q hQ hA4 hA3 x hrec u hu ε hε
