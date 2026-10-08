-- Prove2me | solution 1 for MomentDRO.WorstCov.exists_optimal_tight
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T05:35:26.052014+00:00
-- url     : https://prove2.me/submissions/a09ff1d8-e76c-4f1e-a187-22246f482f36

import Definitions.Def_MomentDRO_WorstCov_Setting

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
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma block_top_psd {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ) (v : ℝ)
    (h : (bordered L l v).PosSemidef) : L.PosSemidef := by
  have he : (bordered L l v).submatrix Sum.inl Sum.inl = L := by
    ext i j
    simp [bordered,Matrix.submatrix,Matrix.fromBlocks]
  rw [← he]
  exact h.submatrix Sum.inl

lemma feasible_diagonal_bounds {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (γ : ℝ) (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
    (v : Fin K → ℝ) (hf : Feasible19 μ Sig γ L l v) (k : Fin K) (i : Fin n) :
    0 ≤ L k i i ∧ L k i i ≤ γ*Sig i i+(μ i)^2 := by
  have hn (j : Fin K) : 0 ≤ L j i i := (block_top_psd _ _ _ (hf.2.2 j)).diag_nonneg
  have hs := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ k)
  have hp : (γ • Sig+Matrix.vecMulVec μ μ-∑ j,L j).PosSemidef := hf.1
  have hd : 0 ≤ (γ • Sig+Matrix.vecMulVec μ μ-∑ j,L j) i i := hp.diag_nonneg
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,Matrix.sum_apply] at hd
  exact ⟨hn k,by nlinarith⟩

lemma feasible_first_squared {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (γ : ℝ) (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
    (v : Fin K → ℝ) (hf : Feasible19 μ Sig γ L l v) (k : Fin K) (i : Fin n) :
    (l k i)^2 ≤ L k i i*v k := by
  have h := psd_entry_squared (bordered (L k) (l k) (v k)) (hf.2.2 k)
    (Sum.inl i) (Sum.inr (0 : Fin 1))
  simpa [bordered,Matrix.fromBlocks] using h

lemma feasible_uniform_bounds {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (γ : ℝ) (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
    (v : Fin K → ℝ) (hf : Feasible19 μ Sig γ L l v) :
    1 ≤ (1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|) ∧
    ∀ k, (∀ i j, |L k i j| ≤ (1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|)) ∧
      (∀ i, |l k i| ≤ (1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|)) ∧
      |v k| ≤ (1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|) := by
  let B := 1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|
  have hB : 1 ≤ B := by
    have hs : 0 ≤ ∑ i : Fin n, |γ*Sig i i+(μ i)^2| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp [B]
    linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hb (i : Fin n) : γ*Sig i i+(μ i)^2 ≤ B := by
    have hsum := Finset.single_le_sum (fun j _ => abs_nonneg (γ*Sig j j+(μ j)^2)) (Finset.mem_univ i)
    have h := le_abs_self (γ*Sig i i+(μ i)^2)
    dsimp [B]
    linarith
  have hd (k : Fin K) (i : Fin n) : 0 ≤ L k i i ∧ L k i i ≤ B := by
    have h := feasible_diagonal_bounds μ Sig γ L l v hf k i
    exact ⟨h.1,h.2.trans (hb i)⟩
  refine ⟨hB,?_⟩
  intro k
  refine ⟨?_,?_,?_⟩
  · intro i j
    have hp := psd_entry_squared (L k) (block_top_psd _ _ _ (hf.2.2 k)) i j
    have hm := mul_le_mul (hd k i).2 (hd k j).2 (hd k j).1 hB0
    apply abs_le_of_sq_le_sq _ hB0
    nlinarith
  · intro i
    have hp := feasible_first_squared μ Sig γ L l v hf k i
    have hm := mul_le_mul (hd k i).2 (weights_bounded μ Sig γ L l v hf k)
      (weights_nonnegative μ Sig γ L l v hf k) hB0
    apply abs_le_of_sq_le_sq _ hB0
    nlinarith
  · rw [abs_of_nonneg (weights_nonnegative μ Sig γ L l v hf k)]
    exact (weights_bounded μ Sig γ L l v hf k).trans hB

end MomentWorstCodex


end


section
set_option autoImplicit false
open Matrix
namespace MomentWorstCodex
lemma psd_set_closed {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed {A : Matrix ι ι ℝ | A.PosSemidef} := by
  have he : {A : Matrix ι ι ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ q : ι → ℝ, {A | 0 ≤ q ⬝ᵥ (A *ᵥ q)} := by
    ext A
    simp [Matrix.posSemidef_iff_dotProduct_mulVec,Matrix.IsHermitian,star_trivial]
  rw [he]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro q
    exact isClosed_le continuous_const (by fun_prop)
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
abbrev Var19 (n K : ℕ) := (Fin K → Matrix (Fin n) (Fin n) ℝ) ×
  (Fin K → Fin n → ℝ) × (Fin K → ℝ)

def programSet {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) :
    Set (Var19 n K) := {z | Feasible19 μ Sig γ z.1 z.2.1 z.2.2}

lemma program_closed {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) :
    IsClosed (programSet (K:=K) μ Sig γ) := by
  have hcov : IsClosed {z : Var19 n K | (γ • Sig+Matrix.vecMulVec μ μ-∑ k,z.1 k).PosSemidef} :=
    psd_set_closed.preimage (by fun_prop)
  have hmean : IsClosed {z : Var19 n K | ∑ k,z.2.1 k = μ} := isClosed_eq (by fun_prop) continuous_const
  have hmass : IsClosed {z : Var19 n K | ∑ k,z.2.2 k = 1} := isClosed_eq (by fun_prop) continuous_const
  have hblocks : IsClosed (⋂ k : Fin K, {z : Var19 n K | (bordered (z.1 k) (z.2.1 k) (z.2.2 k)).PosSemidef}) := by
    apply isClosed_iInter
    intro k
    apply psd_set_closed.preimage
    apply continuous_matrix
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · change Continuous (fun z : Var19 n K => z.1 k i j)
      fun_prop
    · change Continuous (fun z : Var19 n K => z.2.1 k i)
      fun_prop
    · change Continuous (fun z : Var19 n K => z.2.1 k j)
      fun_prop
    · change Continuous (fun z : Var19 n K => z.2.2 k)
      fun_prop
  simpa only [programSet,Feasible19,MomentDRO.Conf.LoewnerLE,
    HighDimStat.RandomMatrices.LoewnerLE,Set.ofPred_and,Set.ofPred_forall] using
      hcov.inter ((hmean.inter hmass).inter hblocks)

lemma program_compact {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) :
    IsCompact (programSet (K:=K) μ Sig γ) := by
  let B := 1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|
  let C₁ : Set (Fin K → Matrix (Fin n) (Fin n) ℝ) := Set.pi Set.univ (fun _ => (Set.Icc (-B) B).matrix)
  let C₂ : Set (Fin K → Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (-B) B))
  let C₃ : Set (Fin K → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-B) B)
  have hI : IsCompact (Set.Icc (-B) B) := isCompact_Icc
  have hM : IsCompact ((Set.Icc (-B) B).matrix : Set (Matrix (Fin n) (Fin n) ℝ)) := hI.matrix
  have hc₁ : IsCompact C₁ := by
    convert isCompact_pi_infinite (fun _ : Fin K => hM) using 1
    ext z; simp [C₁]
  have hc₂ : IsCompact C₂ := by
    convert isCompact_pi_infinite (fun _ : Fin K => isCompact_pi_infinite (fun _ : Fin n => hI)) using 1
    ext z; simp [C₂,Pi.le_def,forall_and]
  have hc₃ : IsCompact C₃ := by
    convert isCompact_pi_infinite (fun _ : Fin K => hI) using 1
    ext z; simp [C₃,Pi.le_def,forall_and]
  apply (hc₁.prod (hc₂.prod hc₃)).of_isClosed_subset (program_closed (K:=K) μ Sig γ)
  intro z hz
  have hb := (feasible_uniform_bounds μ Sig γ z.1 z.2.1 z.2.2 hz).2
  refine ⟨?_,?_,?_⟩
  · intro k hk
    intro i j
    exact abs_le.mp ((hb k).1 i j)
  · intro k hk i hi
    exact abs_le.mp ((hb k).2.1 i)
  · intro k hk
    exact abs_le.mp ((hb k).2.2)
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
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma bordered_zero_psd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) :
    (bordered S 0 0).PosSemidef := by
  let E : Matrix (Fin n) (Fin n ⊕ Fin 1) ℝ := fun i j =>
    match j with
    | .inl k => if i = k then 1 else 0
    | .inr _ => 0
  have he : Eᴴ*S*E = bordered S 0 0 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [E,bordered,Matrix.fromBlocks]
  rw [← he]
  exact hS.conjTranspose_mul_mul_same E

lemma bordered_mean_cov_psd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (μ : Fin n → ℝ) : (bordered (S+Matrix.vecMulVec μ μ) μ 1).PosSemidef := by
  let w : (Fin n ⊕ Fin 1) → ℝ := Sum.elim μ (fun _ => 1)
  have hw : (Matrix.vecMulVec w w).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star w
  have he : bordered (S+Matrix.vecMulVec μ μ) μ 1 = bordered S 0 0+Matrix.vecMulVec w w := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [w,bordered,Matrix.fromBlocks,Matrix.vecMulVec_apply]
  rw [he]
  exact (bordered_zero_psd S hS).add hw

lemma program_feasible {n K : ℕ} [NeZero K] (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (hSig : Sig.PosSemidef) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
      (v : Fin K → ℝ), Feasible19 μ Sig γ L l v := by
  let j := (0 : Fin K)
  let L : Fin K → Matrix (Fin n) (Fin n) ℝ := Pi.single j (γ • Sig+Matrix.vecMulVec μ μ)
  let l : Fin K → Fin n → ℝ := Pi.single j μ
  let v : Fin K → ℝ := Pi.single j 1
  refine ⟨L,l,v,?_,?_,?_⟩
  · change (γ • Sig+Matrix.vecMulVec μ μ-∑ k,L k).PosSemidef
    simpa [L] using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
  · constructor <;> simp [l,v]
  · intro k
    by_cases hk : k = j
    · subst k
      simp only [L,l,v,Pi.single_eq_same]
      exact bordered_mean_cov_psd (γ • Sig) (hSig.smul hγ) μ
    · simp only [L,l,v,Pi.single_eq_of_ne hk]
      exact bordered_zero_psd 0 Matrix.PosSemidef.zero
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma tighten_blocks {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) :
    ∃ L' : Fin K → Matrix (Fin n) (Fin n) ℝ,
      Feasible19 μ Sig γ L' l v ∧ ∑ k,L' k = γ • Sig+Matrix.vecMulVec μ μ := by
  classical
  obtain ⟨j,hj⟩ := positive_weight_exists μ Sig γ L l v hf
  let M := γ • Sig+Matrix.vecMulVec μ μ
  let S := M-∑ k,L k
  have hS : S.PosSemidef := hf.1
  let L' : Fin K → Matrix (Fin n) (Fin n) ℝ := fun k => L k+if k=j then S else 0
  have hs : ∑ k,L' k = M := by
    simp only [L',Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    dsimp [S]
    abel
  have hb : Feasible19 μ Sig γ L' l v := by
    refine ⟨?_,hf.2.1,?_⟩
    · change (M-∑ k,L' k).PosSemidef
      rw [hs,sub_self]
      exact Matrix.PosSemidef.zero
    · intro k
      by_cases hk : k=j
      · subst k
        have he : bordered (L j+S) (l j) (v j) =
            bordered (L j) (l j) (v j)+bordered S 0 0 := by
          ext i r
          rcases i with i | i <;> rcases r with r | r <;>
            simp [bordered,Matrix.fromBlocks,Matrix.add_apply]
        simp only [L',ite_true]
        rw [he]
        exact (hf.2.2 j).add (bordered_zero_psd S hS)
      · simp only [L',if_neg hk,add_zero]
        exact hf.2.2 k
  exact ⟨L',hb,hs⟩

theorem exists_optimal_tight {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2) :
    ∃ (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ),
      Feasible19 μhat Sighat γ2 Lam lam nu ∧
        (∀ (Lam' : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam' : Fin K → Fin n → ℝ)
            (nu' : Fin K → ℝ), Feasible19 μhat Sighat γ2 Lam' lam' nu' →
            obj19 a b x lam' nu' ≤ obj19 a b x lam nu) ∧
        ∑ k, Lam k = γ2 • Sighat + Matrix.vecMulVec μhat μhat := by
  have hn : (programSet (K:=K) μhat Sighat γ2).Nonempty := by
    obtain ⟨L,l,v,hf⟩ := program_feasible (K:=K) μhat Sighat hSig.posSemidef γ2 hγ2.le
    exact ⟨(L,l,v),hf⟩
  have hc : Continuous (fun z : Var19 n K => obj19 a b x z.2.1 z.2.2) := by
    unfold obj19
    fun_prop
  obtain ⟨z,hz,hm⟩ := (hc.upperSemicontinuous.upperSemicontinuousOn
    (programSet (K:=K) μhat Sighat γ2)).exists_isMaxOn hn (program_compact (K:=K) μhat Sighat γ2)
  obtain ⟨L,hf,ht⟩ := tighten_blocks μhat Sighat γ2 z.1 z.2.1 z.2.2 hz
  refine ⟨L,z.2.1,z.2.2,hf,?_,ht⟩
  intro L' l' v' h'
  exact isMaxOn_iff.mp hm (L',l',v') h'
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.WorstCov
theorem solution {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2) :
    ∃ (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ),
      Feasible19 μhat Sighat γ2 Lam lam nu ∧
        (∀ (Lam' : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam' : Fin K → Fin n → ℝ)
            (nu' : Fin K → ℝ), Feasible19 μhat Sighat γ2 Lam' lam' nu' →
            obj19 a b x lam' nu' ≤ obj19 a b x lam nu) ∧
        ∑ k, Lam k = γ2 • Sighat + Matrix.vecMulVec μhat μhat := MomentWorstCodex.exists_optimal_tight a b x μhat Sighat hSig γ2 hγ2

end

#print axioms solution
