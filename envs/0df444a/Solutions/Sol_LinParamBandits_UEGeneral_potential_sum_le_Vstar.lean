-- Prove2me | solution 1 for LinParamBandits.UEGeneral.potential_sum_le_Vstar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:02:28.290813+00:00
-- url     : https://prove2.me/submissions/ef0bc4ea-63b3-4865-86a6-9598499f9c3f

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Definitions.Def_LinParamBandits_UEGeneral_Vstar

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open LinParamBandits.UEGeneral

namespace LPUh
open Matrix LinParamBandits.UEGeneral

variable {r : ℕ}

theorem inner_vec (x y : LinParamBandits.LowerBound.Vec r) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem norm_sq_vec (x : LinParamBandits.LowerBound.Vec r) : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
  rw [← real_inner_self_eq_norm_sq, inner_vec]

theorem design_succ (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    design (fun s : Fin (n + 1) => U s) =
      design (fun s : Fin n => U s) + vecMulVec (U n).ofLp (U n).ofLp := by
  unfold design
  rw [Fin.sum_univ_castSucc]
  simp

theorem quad_design (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) (x : Fin r → ℝ) :
    x ⬝ᵥ (design (fun s : Fin n => U s) *ᵥ x) =
      ∑ s ∈ Finset.range n, ((U s).ofLp ⬝ᵥ x) ^ 2 := by
  unfold design
  rw [Matrix.sum_mulVec, dotProduct_sum, ← Fin.sum_univ_eq_sum_range (fun s => ((U s).ofLp ⬝ᵥ x) ^ 2) n]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vecMulVec_mulVec, dotProduct_smul]
  simp [dotProduct_comm x, sq]

theorem design_psd (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    (design (fun s : Fin n => U s)).PosSemidef := by
  unfold design
  refine Finset.sum_induction _ (fun M : Matrix (Fin r) (Fin r) ℝ => M.PosSemidef)
    (fun _ _ => PosSemidef.add) PosSemidef.zero (fun s _ => ?_)
  have := posSemidef_vecMulVec_self_star (R := ℝ) (U s).ofLp
  simpa using this

end LPUh
namespace LPUh
open Matrix LinParamBandits.UEGeneral

variable {r : ℕ}

theorem design_lower {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 : ℝ}
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (n : ℕ) (hn : r ≤ n) (x : LinParamBandits.LowerBound.Vec r) :
    lam0 * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ (design (fun s : Fin n => U s) *ᵥ x.ofLp) := by
  rw [quad_design]
  refine (hb x).trans ?_
  have h1 : ∑ k : Fin r, inner ℝ (b k) x ^ 2 = ∑ s ∈ Finset.range r, ((U s).ofLp ⬝ᵥ x.ofLp) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => ((U s).ofLp ⬝ᵥ x.ofLp) ^ 2) r]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hU_init k k.2, inner_vec]
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun _ _ _ => sq_nonneg _)

theorem eig_lower {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 : ℝ}
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (n : ℕ) (hn : r ≤ n) (i : Fin r) :
    lam0 ≤ (design_psd U n).isHermitian.eigenvalues i := by
  have hA := (design_psd U n).isHermitian
  have h1 := hA.eigenvalues_eq i
  set v := hA.eigenvectorBasis i with hv
  have hnorm : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have h2 := design_lower hb U hU_init n hn v
  rw [hnorm] at h2
  have h3 : hA.eigenvalues i = v.ofLp ⬝ᵥ (design (fun s : Fin n => U s) *ᵥ v.ofLp) := by
    rw [h1]
    simp
  rw [h3]
  linarith

theorem det_lower {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (n : ℕ) (hn : r ≤ n) :
    lam0 ^ r ≤ (design (fun s : Fin n => U s)).det := by
  have hA := (design_psd U n).isHermitian
  rw [hA.det_eq_prod_eigenvalues]
  have : ∏ _i : Fin r, lam0 ≤ ∏ i : Fin r, ((hA.eigenvalues i : ℝ) : ℝ) :=
    Finset.prod_le_prod (fun _ _ => hlam0.le) (fun i _ => eig_lower hb U hU_init n hn i)
  simpa using this

theorem trace_design (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    (design (fun s : Fin n => U s)).trace = ∑ s ∈ Finset.range n, ‖U s‖ ^ 2 := by
  unfold design
  rw [Matrix.trace_sum, ← Fin.sum_univ_eq_sum_range (fun s => ‖U s‖ ^ 2) n]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [trace_vecMulVec, norm_sq_vec]

theorem det_upper (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    (design (fun s : Fin n => U s)).det ≤ ((design (fun s : Fin n => U s)).trace) ^ r := by
  have hP := design_psd U n
  have hA := hP.isHermitian
  rw [hA.det_eq_prod_eigenvalues]
  have htr : (design (fun s : Fin n => U s)).trace = ∑ i, hA.eigenvalues i := by
    have := hA.trace_eq_sum_eigenvalues
    simpa using this
  have : ∏ i : Fin r, ((hA.eigenvalues i : ℝ) : ℝ) ≤ ∏ _i : Fin r, (design (fun s : Fin n => U s)).trace :=
    Finset.prod_le_prod (fun i _ => hP.eigenvalues_nonneg i) (fun i _ => by
      rw [htr]
      exact Finset.single_le_sum (f := fun j => hA.eigenvalues j) (fun j _ => hP.eigenvalues_nonneg j)
        (Finset.mem_univ i))
  simpa using this

end LPUh
namespace LPUh
open Matrix LinParamBandits.UEGeneral

variable {r : ℕ}

theorem potential_eq (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    potential U n = (U n).ofLp ⬝ᵥ ((design (fun s : Fin n => U s))⁻¹ *ᵥ (U n).ofLp) := rfl

theorem det_pos' {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (n : ℕ) (hn : r ≤ n) :
    0 < (design (fun s : Fin n => U s)).det :=
  lt_of_lt_of_le (pow_pos hlam0 r) (det_lower hlam0 hb U hU_init n hn)

theorem det_succ {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (n : ℕ) (hn : r ≤ n) :
    (design (fun s : Fin (n + 1) => U s)).det =
      (design (fun s : Fin n => U s)).det * (1 + potential U n) := by
  have hdet := det_pos' hlam0 hb U hU_init n hn
  have hu : IsUnit (design (fun s : Fin n => U s)).det := hdet.ne'.isUnit
  rw [design_succ, vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow hu, potential_eq]
  congr 1
  rw [det_unique]
  simp [Matrix.mul_apply, dotProduct, Matrix.mulVec]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end LPUh
namespace LPUh
open Matrix LinParamBandits.UEGeneral

variable {r : ℕ}

theorem potential_bounds {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 ubar : ℝ} (hlam0 : 0 < lam0)
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (hU_norm : ∀ s, ‖U s‖ ≤ ubar) (n : ℕ) (hn : r ≤ n) :
    0 ≤ potential U n ∧ potential U n ≤ ubar ^ 2 / lam0 := by
  have hdet := det_pos' hlam0 hb U hU_init n hn
  have hu : IsUnit (design (fun s : Fin n => U s)).det := hdet.ne'.isUnit
  set A := design (fun s : Fin n => U s) with hA
  set w : Fin r → ℝ := A⁻¹ *ᵥ (U n).ofLp with hw
  set x : LinParamBandits.LowerBound.Vec r := WithLp.toLp 2 w with hx
  have hAw : A *ᵥ w = (U n).ofLp := by
    rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv A hu, one_mulVec]
  have hp : potential U n = (U n).ofLp ⬝ᵥ w := potential_eq U n
  have hp2 : potential U n = w ⬝ᵥ (A *ᵥ w) := by
    calc potential U n = (A *ᵥ w) ⬝ᵥ w := by rw [hp, hAw]
      _ = w ⬝ᵥ (A *ᵥ w) := dotProduct_comm _ _
  have hlow := design_lower hb U hU_init n hn x
  have hxo : x.ofLp = w := rfl
  rw [hxo, ← hp2] at hlow
  have hxn : 0 ≤ ‖x‖ := norm_nonneg _
  have hl0 : 0 ≤ lam0 * ‖x‖ ^ 2 := by positivity
  have hp0 : 0 ≤ potential U n := le_trans hl0 hlow
  refine ⟨hp0, ?_⟩
  have hcs : potential U n ≤ ‖U n‖ * ‖x‖ := by
    rw [hp, ← hxo, ← inner_vec]
    exact real_inner_le_norm _ _
  have hN := hU_norm n
  have hN0 : 0 ≤ ‖U n‖ := norm_nonneg _
  have key : lam0 * potential U n ≤ ‖U n‖ ^ 2 := by
    by_cases hz : potential U n = 0
    · rw [hz, mul_zero]; positivity
    · have hppos : 0 < potential U n := lt_of_le_of_ne hp0 (Ne.symm hz)
      have h1 : (potential U n) ^ 2 ≤ ‖U n‖ ^ 2 * ‖x‖ ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hp0 hcs 2
      have h2 : lam0 * (potential U n) ^ 2 ≤ ‖U n‖ ^ 2 * potential U n := by nlinarith
      nlinarith
  rw [le_div_iff₀ hlam0]
  have : ‖U n‖ ^ 2 ≤ ubar ^ 2 := pow_le_pow_left₀ hN0 hN 2
  nlinarith

end LPUh
namespace LPUh
open Matrix LinParamBandits.UEGeneral

variable {r : ℕ}

theorem det_prod {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (n : ℕ) (hn : r ≤ n) :
    (design (fun s : Fin n => U s)).det =
      (design (fun s : Fin r => U s)).det * ∏ s ∈ Finset.Ico r n, (1 + potential U s) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [det_succ hlam0 hb U hU_init n hn, ih, Finset.prod_Ico_succ_top hn]
    ring

theorem recursion_bound {b : Fin r → LinParamBandits.LowerBound.Vec r} {ubar lam0 : ℝ}
    (hlam0 : 0 < lam0)
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (hU_norm : ∀ s, ‖U s‖ ≤ ubar) (t : ℕ) (ht : r ≤ t) :
    potential U t ≤
      (ubar ^ 2 / lam0 * ((t : ℝ) + 1)) ^ r / ∏ s ∈ Finset.Ico r t, (1 + potential U s) := by
  have hQpos : 0 < ∏ s ∈ Finset.Ico r t, (1 + potential U s) :=
    Finset.prod_pos fun s hs => by
      have := (potential_bounds hlam0 hb U hU_init hU_norm s (Finset.mem_Ico.mp hs).1).1
      linarith
  set Q := ∏ s ∈ Finset.Ico r t, (1 + potential U s) with hQ
  have hp0 := (potential_bounds hlam0 hb U hU_init hU_norm t ht).1
  rw [le_div_iff₀ hQpos]
  have hD1 := det_succ hlam0 hb U hU_init t ht
  have hD2 := det_prod hlam0 hb U hU_init t ht
  have hDr := det_lower hlam0 hb U hU_init r le_rfl
  have hDup := det_upper U (t + 1)
  have htr : (design (fun s : Fin (t + 1) => U s)).trace ≤ ((t : ℝ) + 1) * ubar ^ 2 := by
    rw [trace_design]
    calc ∑ s ∈ Finset.range (t + 1), ‖U s‖ ^ 2 ≤ ∑ s ∈ Finset.range (t + 1), ubar ^ 2 :=
          Finset.sum_le_sum fun s _ => pow_le_pow_left₀ (norm_nonneg _) (hU_norm s) 2
      _ = ((t : ℝ) + 1) * ubar ^ 2 := by simp
  have htr0 : 0 ≤ (design (fun s : Fin (t + 1) => U s)).trace := (design_psd U (t + 1)).trace_nonneg
  have hup : (design (fun s : Fin (t + 1) => U s)).det ≤ (((t : ℝ) + 1) * ubar ^ 2) ^ r :=
    hDup.trans (pow_le_pow_left₀ htr0 htr r)
  have hmain : lam0 ^ r * (potential U t * Q) ≤ (((t : ℝ) + 1) * ubar ^ 2) ^ r := by
    refine le_trans ?_ hup
    rw [hD1, hD2]
    have hDr0 : 0 ≤ (design (fun s : Fin r => U s)).det := le_trans (pow_pos hlam0 r).le hDr
    have h1 : potential U t * Q ≤ Q * (1 + potential U t) := by nlinarith
    calc lam0 ^ r * (potential U t * Q) ≤ (design (fun s : Fin r => U s)).det * (Q * (1 + potential U t)) :=
          mul_le_mul hDr h1 (by positivity) hDr0
      _ = _ := by ring
  have hlr : 0 < lam0 ^ r := pow_pos hlam0 r
  have : (ubar ^ 2 / lam0 * ((t : ℝ) + 1)) ^ r = (((t : ℝ) + 1) * ubar ^ 2) ^ r / lam0 ^ r := by
    rw [← div_pow]; congr 1; field_simp
  rw [this, le_div_iff₀ hlr]
  linarith

end LPUh
namespace LPUh
open Matrix LinParamBandits.UEGeneral

theorem prod_Iio_fin {m : ℕ} (s : Fin m) (f : ℕ → ℝ) :
    ∏ q ∈ Finset.Iio s, f (q : ℕ) = ∏ q ∈ Finset.range (s : ℕ), f q := by
  have h := Finset.prod_map (Finset.Iio s) Fin.valEmbedding f
  rw [Fin.map_valEmbedding_Iio] at h
  have e : Finset.Iio (s : ℕ) = Finset.range s := by ext q; simp
  rw [e] at h
  simpa using h.symm

end LPUh

theorem solution {r : ℕ} (hr : 2 ≤ r) {b : Fin r → LinParamBandits.LowerBound.Vec r} {ubar lam0 : ℝ} (hubar : 0 < ubar)
    (hlam0 : 0 < lam0) (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (hU_norm : ∀ s, ‖U s‖ ≤ ubar)
    (T : ℕ) (hT : r + 1 ≤ T) :
    ∑ t ∈ Finset.Ico r T, potential U t ≤ Vstar r (ubar ^ 2 / lam0) (T - r) := by
  set m := T - r with hm
  set c := ubar ^ 2 / lam0 with hc
  have hc0 : 0 ≤ c := by positivity
  let y : Fin m → ℝ := fun s => potential U (r + (s : ℕ))
  have hfeas : y ∈ VstarFeasible r c m := by
    intro s
    have hb1 := LPUh.potential_bounds hlam0 hb U hU_init hU_norm (r + (s : ℕ)) (Nat.le_add_right _ _)
    have hb2 := LPUh.recursion_bound hlam0 hb U hU_init hU_norm (r + (s : ℕ)) (Nat.le_add_right _ _)
    refine ⟨hb1.1, hb1.2, ?_⟩
    have hprod : ∏ q ∈ Finset.Iio s, (1 + y q) = ∏ q ∈ Finset.Ico r (r + (s : ℕ)), (1 + potential U q) := by
      have := LPUh.prod_Iio_fin s (fun q => 1 + potential U (r + q))
      simp only [y]
      rw [this, Finset.prod_Ico_eq_prod_range]
      simp
    rw [hprod]
    convert hb2 using 3
    push_cast
    ring
  have hsum : ∑ t ∈ Finset.Ico r T, potential U t = ∑ s, y s := by
    rw [Finset.sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range (fun s => potential U (r + s)) m]
  rw [hsum]
  unfold Vstar
  apply le_csSup
  · refine ⟨(m : ℝ) * c, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    calc ∑ s, z s ≤ ∑ _s : Fin m, c := Finset.sum_le_sum fun s _ => (hz s).2.1
      _ = (m : ℝ) * c := by simp
  · exact ⟨y, hfeas, rfl⟩
