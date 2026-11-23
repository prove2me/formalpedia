-- Prove2me | solution 1 for GrothendieckLB.Supplement.grothendieck_bound_of_rounded_correlation
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:46:11.814808+00:00
-- url     : https://prove2.me/submissions/e734f4e5-9daf-4b5a-9542-fb14332e7b21

import Definitions.Def_GrothendieckConstantDefs
import Mathlib.Analysis.Matrix.Order
import Mathlib
open GrothendieckConstant MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology
set_option maxHeartbeats 500000
namespace CorrelationRounding
/- The Schur-power and real Gram arguments follow the public proof of Krivine's bound on Prove2Me. -/
variable {ι : Type*} [Fintype ι]

lemma psd_entrywise_pow (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (k : ℕ) :
    Matrix.PosSemidef (fun i j => G i j ^ k) := by
  induction k with
  | zero =>
    have he : (fun i j => G i j ^ 0 : Matrix ι ι ℝ) =
        Matrix.vecMulVec (fun _ : ι => (1:ℝ)) (star (fun _ : ι => (1:ℝ))) := by
      ext i j; simp [Matrix.vecMulVec]
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star _
  | succ k hk =>
    have he : (fun i j => G i j ^ (k+1) : Matrix ι ι ℝ) =
        (fun i j => G i j ^ k) ⊙ G := by
      ext i j; simp [pow_succ, Matrix.hadamard]
    rw [he]
    exact hk.hadamard hG

section Factorization
open scoped MatrixOrder

/-- Columns of the positive square root realize any finite real PSD matrix. -/
lemma exists_gram (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    ∃ w : ι → EuclideanSpace ℝ ι, ∀ i j, inner ℝ (w i) (w j) = B i j := by
  classical
  let R := CFC.sqrt B
  have hR : R.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian
  have hsq : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  refine ⟨fun i => WithLp.toLp 2 (R.transpose i), ?_⟩
  intro i j
  rw [inner_matrix_col_col, hR, hsq]

end Factorization

lemma exists_unit_gram (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (hdiag : ∀ i, B i i = 1) :
    ∃ w : ι → EuclideanSpace ℝ (Fin (Fintype.card ι)),
      (∀ i, ‖w i‖ = 1) ∧ (∀ i j, inner ℝ (w i) (w j) = B i j) := by
  classical
  obtain ⟨w, hw⟩ := exists_gram B hB
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  refine ⟨fun i => e (w i), ?_, ?_⟩
  · intro i
    rw [e.norm_map]
    have h := hw i i
    rw [real_inner_self_eq_norm_sq, hdiag] at h
    nlinarith [norm_nonneg (w i)]
  · intro i j
    rw [e.inner_map_map, hw]

theorem optSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (optSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨x, y, hx, hy, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 := le_abs_self (A i j)
  have h2 := neg_abs_le (A i j)
  rcases hx i with h | h <;> rcases hy j with h' | h' <;> rw [h, h'] <;> linarith


theorem sdpSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (sdpSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨d, u, v, hu, hv, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 : |inner ℝ (u i) (v j)| ≤ 1 := by
    have := abs_real_inner_le_norm (u i) (v j)
    rw [hu i, hv j] at this
    simpa using this
  calc A i j * inner ℝ (u i) (v j) ≤ |A i j * inner ℝ (u i) (v j)| := le_abs_self _
    _ = |A i j| * |inner ℝ (u i) (v j)| := abs_mul _ _
    _ ≤ |A i j| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |A i j| := mul_one _


theorem one_le_of_isGrothendieckBound {K : ℝ} (hK : IsGrothendieckBound K) : 1 ≤ K := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
  have hmem : (1 : ℝ) ∈ optSet A := by
    refine ⟨fun _ => 1, fun _ => 1, fun _ => Or.inl rfl, fun _ => Or.inl rfl, ?_⟩
    simp [A]
  have hopt : optValue A = 1 := by
    apply le_antisymm
    · apply csSup_le ⟨1, hmem⟩
      rintro s ⟨x, y, hx, hy, rfl⟩
      simp only [A, Fin.sum_univ_one, one_mul]
      rcases hx 0 with h | h <;> rcases hy 0 with h' | h' <;> rw [h, h'] <;> norm_num
    · exact le_csSup (optSet_bdd A) hmem
  let v : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.norm_eq]
  have hsdp : 1 ≤ sdpValue A := by
    apply le_csSup (sdpSet_bdd A)
    refine ⟨1, fun _ => v, fun _ => v, fun _ => hv, fun _ => hv, ?_⟩
    simp [A, hv]
  have h := hK 1 1 A
  rw [hopt, mul_one] at h
  exact hsdp.trans h


lemma sdpSet_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : (sdpSet A).Nonempty := by
  let e : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_eq]
  exact ⟨_, 1, (fun _ => e), (fun _ => e), (fun _ => he), (fun _ => he), rfl⟩


private theorem inner_le_one {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    |inner ℝ u v| ≤ 1 := by simpa only [hu,hv,mul_one] using abs_real_inner_le_norm u v

private theorem reflect_mem {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {x : ℝ} (hx : x ∈ sdpSet A) : -x ∈ sdpSet A := by
  obtain ⟨d,u,v,hu,hv,rfl⟩ := hx
  refine ⟨d,(fun i => -(u i)),v,(fun i => by simp [hu]),hv,?_⟩
  simp only [inner_neg_left,mul_neg,Finset.sum_neg_distrib]

private theorem abs_le_sdp {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {x : ℝ} (hx : x ∈ sdpSet A) :
    |x| ≤ sdpValue A := abs_le.mpr ⟨neg_le.mp (le_csSup (sdpSet_bdd A) (reflect_mem hx)),le_csSup (sdpSet_bdd A) hx⟩

private theorem obj_pow {m n d : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖=1) (hv : ∀ j, ‖v j‖=1) (k : ℕ) :
    |∑ i, ∑ j, A i j*(inner ℝ (u i) (v j))^k| ≤ sdpValue A := by
  let w := Sum.elim u v
  let G := Matrix.gram ℝ w
  let B : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ := fun i j => G i j ^ k
  have hG := psd_entrywise_pow G (Matrix.posSemidef_gram ℝ w) k
  have hd (i : Fin m ⊕ Fin n) : B i i=1 := by
    cases i with
    | inl i => simp [B,G,w,Matrix.gram_apply,hu]
    | inr j => simp [B,G,w,Matrix.gram_apply,hv]
  obtain ⟨z,hz,hB⟩ := exists_unit_gram B hG hd
  apply abs_le_sdp
  refine ⟨_,(fun i => z (Sum.inl i)),(fun j => z (Sum.inr j)),fun i => hz _,fun j => hz _,?_⟩
  simp only [hB,B,G,w,Matrix.gram_apply,Sum.elim_inl,Sum.elim_inr]

private theorem sdp_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ sdpValue A := by
  obtain ⟨s,hs⟩ := sdpSet_nonempty A
  exact (abs_nonneg s).trans (abs_le_sdp hs)

private theorem ler_of_lt_one {a c : ℝ} (h : ∀ r : ℝ, 0 < r → r < 1 → r*a ≤ c) : a ≤ c := by
  have hd : Tendsto (fun r : ℝ => r*a) (𝓝[<] 1) (𝓝 (1*a)) := (continuous_id.mul continuous_const).continuousAt.continuousWithinAt
  have hpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r := (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ in 𝓝[<] 1, r < 1 := self_mem_nhdsWithin
  have hl := le_of_tendsto hd (hpos.and hlt |>.mono (fun r hr => h r hr.1 hr.2))
  simpa only [one_mul] using hl

private theorem objective_limit {m n d : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖=1) (hv : ∀ j, ‖v j‖=1) (H : ℝ → ℝ) (b : ℕ → ℝ)
    (hser : ∀ t : ℝ, |t| < 1 → HasSum (fun k => b k*t^k) (H t))
    (hzero : b 0=0) (hs : Summable (fun k : ℕ => |b (k+2)|))
    (hb : ∀ r : ℝ, 0 < r → r < 1 →
      (∑ i, ∑ j, A i j*H (r*inner ℝ (u i) (v j))) ≤ Real.pi/2*optValue A) :
    b 1*(∑ i, ∑ j, A i j*inner ℝ (u i) (v j)) ≤
      Real.pi/2*optValue A+(∑' k, |b (k+2)|)*sdpValue A := by
  let T (i : Fin m) (j : Fin n) := inner ℝ (u i) (v j)
  let obj (k : ℕ) := ∑ i, ∑ j, A i j*(T i j)^k
  have objb (k : ℕ) : |obj k| ≤ sdpValue A := obj_pow A u v hu hv k
  apply ler_of_lt_one
  intro r hr0 hr
  let a (k : ℕ) := b k*r^k*obj k
  let target := ∑ i, ∑ j, A i j*H (r*(T i j))
  have atij (i : Fin m) (j : Fin n) : HasSum (fun k => A i j*(b k*(r*T i j)^k)) (A i j*H (r*T i j)) := by
    apply (hser _ ?_).mul_left
    rw [abs_mul,abs_of_pos hr0]
    exact (mul_le_of_le_one_right hr0.le (inner_le_one _ _ (hu i) (hv j))).trans_lt hr
  have hsum : HasSum a target := by
    have h : HasSum (fun k => ∑ i, ∑ j, A i j*(b k*(r*T i j)^k)) target :=
      hasSum_sum (fun i _ => hasSum_sum (fun j _ => atij i j))
    apply h.congr_fun
    intro k
    dsimp only [a,obj]
    simp only [Finset.mul_sum,mul_pow]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htail (k : ℕ) : -(a (k+2)) ≤ |b (k+2)| *sdpValue A := by
    calc _ ≤ |a (k+2)| := neg_le_abs _
         _ = (|b (k+2)| *r^(k+2))*|obj (k+2)| := by simp only [a,abs_mul,abs_pow,abs_of_pos hr0]
         _ ≤ |b (k+2)| *sdpValue A := mul_le_mul
           (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hr0.le hr.le))
           (objb _) (abs_nonneg _) (abs_nonneg _)
  have hlow := (((summable_nat_add_iff 2).mpr hsum.summable).neg).tsum_le_tsum htail (hs.mul_right (sdpValue A))
  rw [tsum_neg,hs.tsum_mul_right] at hlow
  have hsplit := hsum.summable.sum_add_tsum_nat_add 2
  rw [hsum.tsum_eq,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero] at hsplit
  have h0 : a 0=0 := by simp [a,hzero]
  have h1 : a 1=b 1*r*(∑ i, ∑ j, A i j*inner ℝ (u i) (v j)) := by simp [a,obj,T]
  rw [h0,h1] at hsplit
  have hk : target ≤ Real.pi/2*optValue A := hb r hr0 hr
  linarith only [hlow,hsplit,hk]

end CorrelationRounding

open CorrelationRounding in
theorem solution (H : ℝ → ℝ) (b : ℕ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hser : ∀ t : ℝ, |t| < 1 → HasSum (fun k => b k*t^k) (H t))
    (hzero : b 0=0) (hs : Summable (fun k : ℕ => |b (k+2)|))
    (hgap : γ+(∑' k, |b (k+2)|) ≤ b 1)
    (hround : ∀ (m n d : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
      (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖u i‖=1) → (∀ j, ‖v j‖=1) → ∀ r : ℝ, 0 < r → r < 1 →
        (∑ i, ∑ j, A i j*H (r*inner ℝ (u i) (v j))) ≤ Real.pi/2*optValue A) :
    grothendieckConst ≤ Real.pi/(2*γ) := by
  apply csInf_le ⟨1,fun K hK => one_le_of_isGrothendieckBound hK⟩
  intro m n A
  let D := ∑' k, |b (k+2)|
  have hD : 0 ≤ D := tsum_nonneg fun _ => abs_nonneg _
  have hb : 0 < b 1 := (add_pos_of_pos_of_nonneg hγ hD).trans_le hgap
  have hsup : sdpValue A ≤ (Real.pi/2*optValue A+D*sdpValue A)/(b 1) := by
    apply csSup_le (sdpSet_nonempty A)
    rintro x ⟨d,u,v,hu,hv,rfl⟩
    apply (le_div_iff₀ hb).mpr
    rw [mul_comm]
    exact objective_limit A u v hu hv H b hser hzero hs (hround m n d A u v hu hv)
  have hh := (le_div_iff₀ hb).mp hsup
  have hh' := mul_le_mul_of_nonneg_right hgap (sdp_nonneg A)
  change sdpValue A ≤ Real.pi/(2*γ)*optValue A
  rw [show Real.pi/(2*γ)*optValue A = (Real.pi/2*optValue A)/γ by ring,le_div_iff₀ hγ]
  dsimp only [D] at hh
  nlinarith only [hh,hh']

