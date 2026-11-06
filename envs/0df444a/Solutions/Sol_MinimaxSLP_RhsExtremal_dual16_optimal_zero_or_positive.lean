-- Prove2me | solution 1 for MinimaxSLP.RhsExtremal.dual16_optimal_zero_or_positive
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:56:55.729331+00:00
-- url     : https://prove2.me/submissions/8383d532-d1e4-43b7-8d90-a6e32f97a9b1

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model

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

end RhsExtH


open Matrix MinimaxSLP.ObjSDP MinimaxSLP.RhsExtremal

namespace RhsExtH

variable {r : ℕ}

lemma bord_sum2 {K N : ℕ} (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)) :
    ∑ k, ∑ i, bordered (s k i).1 (s k i).2.1 (s k i).2.2 =
      bordered (∑ k, ∑ i, (s k i).1) (∑ k, ∑ i, (s k i).2.1) (∑ k, ∑ i, (s k i).2.2) := by
  ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.sum_apply, Finset.sum_apply]

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

open RhsExtH

lemma cont_bord {r K N : ℕ} (k : Fin K) (i : Fin N) :
    Continuous (fun s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) =>
      bordered (s k i).1 (s k i).2.1 (s k i).2.2) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  rcases a with a | a <;> rcases b with b | b <;> simp only [bord_ll, bord_lr, bord_rl, bord_rr]
  all_goals fun_prop

lemma feas_closed {r K N : ℕ} (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ) :
    IsClosed (feasible16 K N μ Q) := by
  have : feasible16 K N μ Q =
      {s | ∑ k, ∑ i, bordered (s k i).1 (s k i).2.1 (s k i).2.2 = bordered Q μ 1} ∩
        ⋂ k, ⋂ i, (fun s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) =>
          bordered (s k i).1 (s k i).2.1 (s k i).2.2) ⁻¹' {M | M.PosSemidef} := by
    ext s; simp [feasible16]
  rw [this]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const)
    (isClosed_iInter fun k => isClosed_iInter fun i => isClosed_psd.preimage (cont_bord k i))
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun i _ => cont_bord k i

lemma feas_bound {r K N : ℕ} (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ))
    (hs : s ∈ feasible16 K N μ Q) (k : Fin K) (i : Fin N) (a b : Fin r ⊕ Fin 1) :
    |bordered (s k i).1 (s k i).2.1 (s k i).2.2 a b| ≤ ∑ c, |bordered Q μ 1 c c| := by
  obtain ⟨hsum, hpsd⟩ := hs
  set B := fun k i => bordered (s k i).1 (s k i).2.1 (s k i).2.2
  have hdiag : ∀ c, B k i c c ≤ ∑ c, |bordered Q μ 1 c c| := by
    intro c
    have e : bordered Q μ 1 c c = ∑ k, ∑ i, B k i c c := by
      rw [← hsum]; simp [B, Matrix.sum_apply]
    have h1 : B k i c c ≤ ∑ i, B k i c c :=
      Finset.single_le_sum (f := fun i => B k i c c) (fun i _ => (hpsd k i).diag_nonneg) (Finset.mem_univ i)
    have h2 : ∑ i, B k i c c ≤ ∑ k, ∑ i, B k i c c :=
      Finset.single_le_sum (f := fun k => ∑ i, B k i c c)
        (fun k _ => Finset.sum_nonneg fun i _ => (hpsd k i).diag_nonneg) (Finset.mem_univ k)
    have h3 : bordered Q μ 1 c c ≤ |bordered Q μ 1 c c| := le_abs_self _
    have h4 : |bordered Q μ 1 c c| ≤ ∑ c, |bordered Q μ 1 c c| :=
      Finset.single_le_sum (f := fun c => |bordered Q μ 1 c c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
    linarith
  have := psd_entry_bound (hpsd k i) a b
  have ha := hdiag a; have hb := hdiag b
  simp only [B] at ha hb
  linarith

lemma feas_compact {r K N : ℕ} (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ) :
    IsCompact (feasible16 K N μ Q) := by
  set C := ∑ c, |bordered Q μ 1 c c|
  let Box : Set (Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-C) C) ×ˢ
        ((Set.pi Set.univ fun _ => Set.Icc (-C) C) ×ˢ Set.Icc (-C) C)
  have hBox : IsCompact Box :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).prod
        ((isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_Icc)
  refine hBox.of_isClosed_subset (feas_closed μ Q) ?_
  intro s hs
  intro k _ i _
  have hb := feas_bound μ Q s hs k i
  refine ⟨fun a _ b _ => ?_, fun a _ => ?_, ?_⟩
  · have := hb (Sum.inl a) (Sum.inl b); simp only [bord_ll] at this
    exact Set.mem_Icc.mpr (abs_le.mp this)
  · have := hb (Sum.inl a) (Sum.inr 0); simp only [bord_lr] at this
    exact Set.mem_Icc.mpr (abs_le.mp this)
  · have := hb (Sum.inr 0) (Sum.inr 0); simp only [bord_rr] at this
    exact Set.mem_Icc.mpr (abs_le.mp this)

lemma obj16_cont {r n K N : ℕ} (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ)
    (ps : Fin N → Fin r → ℝ) (x : Fin n → ℝ) : Continuous (obj16 T α β ps x) := by
  unfold obj16
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun i _ => ?_
  simp only [dotProduct]
  fun_prop

lemma M0_psd {r : ℕ} (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef) :
    (bordered Q μ 1).PosSemidef := by
  refine bord_psd_of hQ fun a t => ?_
  have h1 := hA4.posSemidef.dotProduct_mulVec_nonneg a
  rw [star_trivial, sub_mulVec, dotProduct_sub, vecMulVec_mulVec] at h1
  have e : a ⬝ᵥ (MulOpposite.op (μ ⬝ᵥ a) • μ) = (μ ⬝ᵥ a) * (μ ⬝ᵥ a) := by
    rw [dotProduct_comm]; simp [smul_dotProduct, dotProduct_comm]
  rw [e] at h1
  nlinarith [sq_nonneg (μ ⬝ᵥ a + t)]

theorem M3 {r n K N : ℕ} [NeZero K]
    (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hN : 0 < N)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (x : Fin n → ℝ) :
    ∃ s ∈ feasible16 K N μ Q,
      IsGreatest (obj16 T α β ps x '' feasible16 K N μ Q) (obj16 T α β ps x s) ∧
      ∀ k i, 0 < (s k i).2.2 ∨ s k i = 0 := by
  classical
  set i0 : Fin N := ⟨0, hN⟩
  -- nonempty
  set s0 : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :=
    fun k i => if k = 0 ∧ i = i0 then (Q, μ, 1) else 0 with hs0
  have hs0F : s0 ∈ feasible16 K N μ Q := by
    rw [feas_iff]
    refine ⟨⟨?_, ?_, ?_⟩, fun k i => ?_⟩
    · simp [s0, apply_ite Prod.fst, ite_and, Finset.sum_ite_eq']
    · simp [s0, apply_ite Prod.snd, apply_ite Prod.fst, ite_and, Finset.sum_ite_eq']
    · simp [s0, apply_ite Prod.snd, ite_and, Finset.sum_ite_eq']
    · by_cases h : k = 0 ∧ i = i0
      · simp only [s0, if_pos h]; exact M0_psd μ Q hQ hA4
      · simp only [s0, if_neg h, Prod.fst_zero, Prod.snd_zero, bord_zero]; exact PosSemidef.zero
  obtain ⟨s1, hs1F, hmax⟩ := (feas_compact (K := K) (N := N) μ Q).exists_isMaxOn ⟨s0, hs0F⟩
    (obj16_cont T α β ps x).continuousOn
  obtain ⟨⟨hV1, hv1, hw1⟩, hpsd1⟩ := (feas_iff μ Q s1).mp hs1F
  set P : Fin K → Fin N → Prop := fun k i => 0 < (s1 k i).2.2
  have hnonP : ∀ k i, ¬ P k i → (s1 k i).2.2 = 0 ∧ (s1 k i).2.1 = 0 := by
    intro k i hk
    have h0 : (s1 k i).2.2 = 0 := le_antisymm (not_lt.mp hk) (bord_v0_nonneg (hpsd1 k i))
    refine ⟨h0, ?_⟩
    have := hpsd1 k i; rw [h0] at this; exact bord_v_zero this
  obtain ⟨k1, i1, hP1⟩ : ∃ k i, P k i := by
    by_contra hcon
    push_neg at hcon
    have : ∑ k, ∑ i, (s1 k i).2.2 ≤ 0 :=
      Finset.sum_nonpos fun k _ => Finset.sum_nonpos fun i _ => not_lt.mp (hcon k i)
    linarith
  set E : Matrix (Fin r) (Fin r) ℝ := ∑ k, ∑ i, if P k i then 0 else (s1 k i).1
  have hEpsd : E.PosSemidef := by
    refine posSemidef_sum _ fun k _ => posSemidef_sum _ fun i _ => ?_
    split_ifs
    · exact PosSemidef.zero
    · exact bord_V_psd (hpsd1 k i)
  set s2 : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :=
    fun k i => if P k i then
      (if k = k1 ∧ i = i1 then ((s1 k i).1 + E, (s1 k i).2.1, (s1 k i).2.2) else s1 k i) else 0
  have hsnd : ∀ k i, (s2 k i).2 = (s1 k i).2 := by
    intro k i
    by_cases hp : P k i
    · simp only [s2, if_pos hp]; split_ifs <;> rfl
    · obtain ⟨h1, h2⟩ := hnonP k i hp
      simp only [s2, if_neg hp, Prod.snd_zero]
      ext <;> simp [h1, h2]
  have hfst : ∀ k i, (s2 k i).1 = (if P k i then (s1 k i).1 else 0) +
      (if k = k1 ∧ i = i1 then E else 0) := by
    intro k i
    by_cases hp : P k i
    · by_cases hki : k = k1 ∧ i = i1
      · obtain ⟨rfl, rfl⟩ := hki; simp [s2, hp]
      · simp [s2, hp, hki]
    · have : ¬ (k = k1 ∧ i = i1) := by rintro ⟨rfl, rfl⟩; exact hp hP1
      simp [s2, hp, this]
  have hobj : obj16 T α β ps x s2 = obj16 T α β ps x s1 := by
    unfold obj16
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    rw [show (s2 k i).2.1 = (s1 k i).2.1 from congrArg Prod.fst (hsnd k i),
      show (s2 k i).2.2 = (s1 k i).2.2 from congrArg Prod.snd (hsnd k i)]
  have hs2F : s2 ∈ feasible16 K N μ Q := by
    rw [feas_iff]
    refine ⟨⟨?_, ?_, ?_⟩, fun k i => ?_⟩
    · have hE1 : ∑ k, ∑ i, (if k = k1 ∧ i = i1 then E else 0) = E := by
        rw [Fintype.sum_eq_single k1, Fintype.sum_eq_single i1]
        · simp
        · intro i hi; simp [hi]
        · intro k hk; simp [hk]
      simp only [hfst, Finset.sum_add_distrib, hE1]
      change _ + ∑ k, ∑ i, (if P k i then 0 else (s1 k i).1) = _
      rw [← hV1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · rw [← hv1]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
        congrArg Prod.fst (hsnd k i)
    · rw [← hw1]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
        congrArg Prod.snd (hsnd k i)
    · by_cases hp : P k i
      · by_cases hki : k = k1 ∧ i = i1
        · simp only [s2, if_pos hp, if_pos hki]
          have : bordered ((s1 k i).1 + E) (s1 k i).2.1 (s1 k i).2.2 =
              bordered (s1 k i).1 (s1 k i).2.1 (s1 k i).2.2 + bordered E 0 0 := by
            rw [← bord_add]; simp
          rw [this]
          refine (hpsd1 k i).add (bord_psd_of ?_ fun a t => ?_)
          · exact isHermitian_iff_isSymm.mp hEpsd.1
          · have := hEpsd.dotProduct_mulVec_nonneg a
            rw [star_trivial] at this
            simpa using this
        · simp only [s2, if_pos hp, if_neg hki]; exact hpsd1 k i
      · simp only [s2, if_neg hp, Prod.fst_zero, Prod.snd_zero, bord_zero]; exact PosSemidef.zero
  refine ⟨s2, hs2F, ⟨⟨s2, hs2F, rfl⟩, ?_⟩, fun k i => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [hobj]; exact hmax hs
  · by_cases hp : P k i
    · left
      rw [show (s2 k i).2.2 = (s1 k i).2.2 from congrArg Prod.snd (hsnd k i)]; exact hp
    · right; simp [s2, hp]

theorem solution {r n K N : ℕ} [NeZero K]
    (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hN : 0 < N)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (x : Fin n → ℝ) :
    ∃ s ∈ feasible16 K N μ Q,
      IsGreatest (obj16 T α β ps x '' feasible16 K N μ Q) (obj16 T α β ps x s) ∧
      ∀ k i, 0 < (s k i).2.2 ∨ s k i = 0 :=
  M3 T α β ps μ Q hN hQ hA4 x
