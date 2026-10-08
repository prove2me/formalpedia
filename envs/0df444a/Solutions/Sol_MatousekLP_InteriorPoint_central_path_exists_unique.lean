-- Prove2me | solution 1 for MatousekLP.InteriorPoint.central_path_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:14:34.274324+00:00
-- url     : https://prove2.me/submissions/d659cd50-bba2-47b1-9238-5d0b841def49

import Mathlib
import Definitions.Def_MatousekLP_InteriorPoint_CentralPath

set_option autoImplicit false

open Matrix
namespace MatousekLP.InteriorPoint

lemma log_affine_upper (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    Real.log t ≤ a * t - 1 - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (mul_pos ha ht)
  rw [Real.log_mul ha.ne' ht.ne'] at h
  linarith

lemma barrier_coordinate_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (yt : Fin m → ℝ)
    (hyt : IsDualInterior A c yt) (μ L : ℝ) (hμ : 0 < μ) :
    ∃ U : Fin n → ℝ, ∀ x, IsPrimalInterior A b x → L ≤ barrier c μ x →
      ∀ j, x j ≤ U j := by
  let s := Aᵀ *ᵥ yt - c
  let a := fun j => s j / (2 * μ)
  let K := ∑ j, (-1 - Real.log (a j))
  refine ⟨fun j => (2 * (yt ⬝ᵥ b + μ * K - L)) / s j, ?_⟩
  intro x hx hL j
  have hs : ∀ i, 0 < s i := hyt
  have ha : ∀ i, 0 < a i := fun i => div_pos (hs i) (by positivity)
  have hlog : ∑ i, Real.log (x i) ≤ ∑ i, (a i * x i - 1 - Real.log (a i)) :=
    Finset.sum_le_sum fun i _ => log_affine_upper _ _ (ha i) (hx.2 i)
  have hsum : μ * ∑ i, (a i * x i - 1 - Real.log (a i)) =
      (s ⬝ᵥ x) / 2 + μ * K := by
    simp only [K, dotProduct, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a]
    field_simp
    <;> ring
  have hdual : s ⬝ᵥ x = yt ⬝ᵥ b - c ⬝ᵥ x := by
    dsimp [s]
    rw [sub_dotProduct, dotProduct_comm (Aᵀ *ᵥ yt) x, dotProduct_transpose_mulVec, hx.1]
  have htotal : s ⬝ᵥ x ≤ 2 * (yt ⬝ᵥ b + μ * K - L) := by
    have := mul_le_mul_of_nonneg_left hlog hμ.le
    rw [hsum] at this
    unfold barrier at hL
    linarith
  have hj : s j * x j ≤ s ⬝ᵥ x :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hs i).le (hx.2 i).le) (Finset.mem_univ j)
  apply (le_div_iff₀ (hs j)).2
  nlinarith

end MatousekLP.InteriorPoint


namespace MatousekLP.InteriorPoint
open Matrix
lemma cp_pos {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {μ : ℝ} {x : Fin n → ℝ} {y : Fin m → ℝ} {s : Fin n → ℝ}
    (hμ : 0 < μ) (h : CentralPathSystem A b c μ x y s) :
    (∀ j, 0 < x j) ∧ ∀ j, 0 < s j := by
  constructor <;> intro j
  · have hp : 0 < s j * x j := by rw [h.2.2.1 j]; exact hμ
    exact (mul_pos_iff.mp hp).resolve_right (by intro hn; linarith [show (0 : ℝ) ≤ x j from h.2.2.2.1 j, hn.2]) |>.2
  · have hp : 0 < s j * x j := by rw [h.2.2.1 j]; exact hμ
    exact (mul_pos_iff.mp hp).resolve_right (by intro hn; linarith [show (0 : ℝ) ≤ x j from h.2.2.2.1 j, hn.2]) |>.1
lemma cp_unique_max {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {c : Fin n → ℝ} {μ : ℝ} {x : Fin n → ℝ} {y : Fin m → ℝ} {s : Fin n → ℝ}
    (hμ : 0 < μ) (h : CentralPathSystem A b c μ x y s) :
    IsUniqueBarrierMaximizer A b c μ x := by
  classical
  obtain ⟨hx, hs⟩ := cp_pos hμ h
  refine ⟨⟨h.1, hx⟩, ?_⟩
  intro z hz hzx
  have hlin : c ⬝ᵥ z - c ⬝ᵥ x = -(s ⬝ᵥ z - s ⬝ᵥ x) := by
    have hz' := dotProduct_transpose_mulVec A z y
    have hx' := dotProduct_transpose_mulVec A x y
    rw [hz.1] at hz'
    rw [h.1] at hx'
    have hc : Aᵀ *ᵥ y = c + s := by rw [← h.2.1]; abel
    rw [hc, dotProduct_add] at hz' hx'
    rw [dotProduct_comm z c, dotProduct_comm z s] at hz'
    rw [dotProduct_comm x c, dotProduct_comm x s] at hx'
    linarith
  have hle : ∀ j, Real.log (z j) - Real.log (x j) ≤ z j / x j - 1 := by
    intro j
    rw [← Real.log_div (hz.2 j).ne' (hx j).ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hz.2 j) (hx j))
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ x j := by
    by_contra hh
    push_neg at hh
    exact hzx (funext hh)
  have hjlt : Real.log (z j) - Real.log (x j) < z j / x j - 1 := by
    rw [← Real.log_div (hz.2 j).ne' (hx j).ne']
    exact Real.log_lt_sub_one_of_pos (div_pos (hz.2 j) (hx j))
      (by intro he; exact hj ((div_eq_one_iff_eq (hx j).ne').mp he))
  have hsum : (∑ j, (Real.log (z j) - Real.log (x j))) < ∑ j, (z j / x j - 1) :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hjlt⟩
  have hmul : μ * (∑ j, (z j / x j - 1)) = s ⬝ᵥ z - s ⬝ᵥ x := by
    rw [Finset.mul_sum, dotProduct, dotProduct, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi := h.2.2.1 i
    have hxi := (hx i).ne'
    rw [← hi]
    field_simp <;> ring
  have hh := mul_lt_mul_of_pos_left hsum hμ
  rw [hmul, Finset.sum_sub_distrib] at hh
  unfold barrier
  linarith
end MatousekLP.InteriorPoint


namespace MatousekLP.InteriorPoint
open Matrix Set
noncomputable def barrierExp {n : ℕ} (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp ((c ⬝ᵥ x) / μ) * ∏ j, x j
lemma barrierExp_continuous {n : ℕ} (c : Fin n → ℝ) (μ : ℝ) : Continuous (barrierExp c μ) := by
  unfold barrierExp dotProduct
  fun_prop
lemma barrierExp_eq {n : ℕ} (c : Fin n → ℝ) (μ : ℝ) (hμ : μ ≠ 0)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    barrierExp c μ x = Real.exp (barrier c μ x / μ) := by
  unfold barrierExp barrier
  have he : ∏ j, x j = Real.exp (∑ j, Real.log (x j)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    exact (Real.exp_log (hx j)).symm
  rw [he, ← Real.exp_add]
  congr 1
  field_simp
lemma barrier_exists_max {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (hμ : 0 < μ) (xt : Fin n → ℝ)
    (hxt : IsPrimalInterior A b xt)
    (hb : Bornology.IsBounded {x | IsPrimalInterior A b x ∧ barrier c μ xt ≤ barrier c μ x}) :
    ∃ x, IsPrimalInterior A b x ∧ ∀ z, IsPrimalInterior A b z → barrier c μ z ≤ barrier c μ x := by
  classical
  let S := {x | IsPrimalInterior A b x ∧ barrier c μ xt ≤ barrier c μ x}
  have hSxt : xt ∈ S := ⟨hxt, le_rfl⟩
  have hcompact : IsCompact (closure S) := hb.isCompact_closure
  have hfeas : closure S ⊆ {x | A *ᵥ x = b ∧ 0 ≤ x} := by
    apply closure_minimal
    · intro x hx
      exact ⟨hx.1.1, fun j => (hx.1.2 j).le⟩
    · apply IsClosed.inter
      · exact isClosed_eq (by fun_prop) continuous_const
      · exact isClosed_le continuous_const continuous_id
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn ⟨xt, subset_closure hSxt⟩
    (barrierExp_continuous c μ).continuousOn
  have hxF : 0 < barrierExp c μ x := by
    have htF : 0 < barrierExp c μ xt := by
      rw [barrierExp_eq c μ hμ.ne' xt hxt.2]
      exact Real.exp_pos _
    exact htF.trans_le (hmax (subset_closure hSxt))
  have hxnonneg := (hfeas hx).2
  have hxpos : ∀ j, 0 < x j := by
    intro j
    by_contra hh
    have hz : x j = 0 := le_antisymm (not_lt.mp hh) (hxnonneg j)
    have hp : (∏ i, x i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hz
    simp [barrierExp, hp] at hxF
  refine ⟨x, ⟨(hfeas hx).1, hxpos⟩, ?_⟩
  have htx : barrier c μ xt ≤ barrier c μ x := by
    have hh := hmax (subset_closure hSxt)
    change barrierExp c μ xt ≤ barrierExp c μ x at hh
    rw [barrierExp_eq c μ hμ.ne' xt hxt.2, barrierExp_eq c μ hμ.ne' x hxpos,
      Real.exp_le_exp, div_le_div_iff_of_pos_right hμ] at hh
    exact hh
  intro z hz
  by_cases ht : barrier c μ xt ≤ barrier c μ z
  · have hh := hmax (subset_closure (show z ∈ S from ⟨hz, ht⟩))
    change barrierExp c μ z ≤ barrierExp c μ x at hh
    rw [barrierExp_eq c μ hμ.ne' z hz.2, barrierExp_eq c μ hμ.ne' x hxpos,
      Real.exp_le_exp, div_le_div_iff_of_pos_right hμ] at hh
    exact hh
  · exact (not_le.mp ht).le.trans htx
end MatousekLP.InteriorPoint


namespace MatousekLP.InteriorPoint
open Matrix
lemma rank_surjective {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m) :
    Function.Surjective (fun x => A *ᵥ x) := by
  have htop : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank, Module.finrank_pi] using hrank
  exact LinearMap.range_eq_top.mp htop
lemma rank_transpose_injective {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hrank : A.rank = m) : Function.Injective (fun y => Aᵀ *ᵥ y) := by
  intro y z hyz
  change Aᵀ *ᵥ y = Aᵀ *ᵥ z at hyz
  have hdiff : Aᵀ *ᵥ (y-z) = 0 := by rw [mulVec_sub, hyz, sub_self]
  obtain ⟨w, hw⟩ := rank_surjective A hrank (y-z)
  change A *ᵥ w = y-z at hw
  have hd : (y-z) ⬝ᵥ (y-z) = 0 := by
    calc (y-z) ⬝ᵥ (y-z) = w ⬝ᵥ (Aᵀ *ᵥ (y-z)) := by
           rw [dotProduct_transpose_mulVec, hw, dotProduct_comm]
         _ = 0 := by rw [hdiff, dotProduct_zero]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hd)
end MatousekLP.InteriorPoint


namespace MatousekLP.InteriorPoint
open Matrix Set Filter
open scoped Topology
noncomputable def linDot {n : ℕ} (v : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, v j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)
lemma linDot_apply {n : ℕ} (v x : Fin n → ℝ) : linDot v x = v ⬝ᵥ x := by
  simp [linDot, dotProduct]
lemma barrier_strict_deriv {n : ℕ} (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) :
    HasStrictFDerivAt (barrier c μ) (linDot (fun j => c j + μ / x j)) x := by
  have hlog : HasStrictFDerivAt (fun z : Fin n → ℝ => ∑ j, Real.log (z j))
      (∑ j, (x j)⁻¹ • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)) x := by
    apply HasStrictFDerivAt.fun_sum
    intro j _
    exact (Real.hasStrictDerivAt_log (hx j).ne').comp_hasStrictFDerivAt x
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)).hasStrictFDerivAt
  have hc := (linDot c).hasStrictFDerivAt (x := x)
  have hh := hc.add (hlog.const_mul μ)
  convert! hh using 1
  · funext z
    simp [barrier, linDot_apply]
  · ext z
    simp [linDot, Finset.mul_sum, Finset.sum_add_distrib, add_mul, div_eq_mul_inv,
      mul_assoc]
lemma barrier_stationary {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (μ : ℝ) (hμ : 0 < μ)
    (x : Fin n → ℝ) (hx : IsPrimalInterior A b x)
    (hmax : ∀ z, IsPrimalInterior A b z → barrier c μ z ≤ barrier c μ x)
    (hinj : Function.Injective (fun y => Aᵀ *ᵥ y)) :
    ∃ y s, CentralPathSystem A b c μ x y s := by
  classical
  have hpos : ∀ᶠ z in 𝓝 x, ∀ j, 0 < z j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (isOpen_lt continuous_const (continuous_apply j)).mem_nhds (hx.2 j)
  have hlocal : IsLocalMaxOn (barrier c μ) {z | ∀ i, (A *ᵥ z) i = (A *ᵥ x) i} x := by
    filter_upwards [hpos.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz ha
    exact hmax z ⟨by simpa [hx.1] using funext ha, hz⟩
  have hrow : ∀ i : Fin m, HasStrictFDerivAt (fun z => (A *ᵥ z) i) (linDot (A i)) x := by
    intro i
    convert (linDot (A i)).hasStrictFDerivAt (x := x) using 1
    funext z
    exact (linDot_apply (A i) z).symm
  obtain ⟨η, η0, hη, he⟩ := IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt
    (show IsLocalExtrOn (barrier c μ) {z | ∀ i, (A *ᵥ z) i = (A *ᵥ x) i} x from hlocal.isExtr) hrow (barrier_strict_deriv c μ x hx.2)
  have hcoord : ∀ j, (Aᵀ *ᵥ η) j + η0 * (c j + μ / x j) = 0 := by
    intro j
    have hh := DFunLike.congr_fun he (Pi.single j 1)
    simpa [linDot, mulVec, dotProduct, Finset.mul_sum, mul_comm, Pi.single_apply,
      transpose_apply] using hh
  have hη0 : η0 ≠ 0 := by
    intro hh
    have ha : Aᵀ *ᵥ η = 0 := by ext j; simpa [hh] using hcoord j
    have hez : η = 0 := hinj (by simpa using ha)
    apply hη
    simp [hez, hh]
  let y : Fin m → ℝ := fun i => -η i / η0
  let s : Fin n → ℝ := fun j => μ / x j
  have hy : ∀ j, (Aᵀ *ᵥ y) j = c j + s j := by
    intro j
    have hh := hcoord j
    have hlin : (Aᵀ *ᵥ y) j = -(Aᵀ *ᵥ η) j / η0 := by
      simp [y, mulVec, dotProduct, Finset.sum_div, ← Finset.sum_neg_distrib,
        mul_div, mul_neg]
    rw [hlin]
    apply (div_eq_iff hη0).mpr
    dsimp [s]
    linarith
  refine ⟨y, s, hx.1, ?_, ?_, fun j => (hx.2 j).le, ?_⟩
  · ext j
    simp only [Pi.sub_apply]
    rw [hy j]
    ring
  · intro j
    dsimp [s]
    exact div_mul_cancel₀ μ (hx.2 j).ne'
  · intro j
    exact (div_pos hμ (hx.2 j)).le
end MatousekLP.InteriorPoint


open Matrix MatousekLP.InteriorPoint

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (xt : Fin n → ℝ) (hxt : IsPrimalInterior A b xt)
    (yt : Fin m → ℝ) (hyt : IsDualInterior A c yt) :
    ∀ μ : ℝ, 0 < μ →
      ∃ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ),
        CentralPathSystem A b c μ x y s ∧
        (∀ (x' : Fin n → ℝ) (y' : Fin m → ℝ) (s' : Fin n → ℝ),
          CentralPathSystem A b c μ x' y' s' → x' = x ∧ y' = y ∧ s' = s) ∧
        IsUniqueBarrierMaximizer A b c μ x := by
  intro μ hμ
  obtain ⟨U, hU⟩ := barrier_coordinate_bound A b c yt hyt μ (barrier c μ xt) hμ
  have hb : Bornology.IsBounded {x | IsPrimalInterior A b x ∧ barrier c μ xt ≤ barrier c μ x} := by
    apply (Bornology.IsBounded.pi (fun j => Metric.isBounded_Icc (0 : ℝ) (U j))).subset
    intro x hx
    exact fun j _ => ⟨(hx.1.2 j).le, hU x hx.1 hx.2 j⟩
  obtain ⟨x, hx, hm⟩ := barrier_exists_max A b c μ hμ xt hxt hb
  obtain ⟨y, s, hsys⟩ := barrier_stationary A b c hrank μ hμ x hx hm
    (rank_transpose_injective A hrank)
  have hmax := cp_unique_max hμ hsys
  refine ⟨x, y, s, hsys, ?_, hmax⟩
  intro x' y' s' hsys'
  have hx' : IsPrimalInterior A b x' := ⟨hsys'.1, (cp_pos hμ hsys').1⟩
  have heqx : x' = x := by
    by_contra hn
    have hlt := hmax.2 x' hx' hn
    have hlt' := (cp_unique_max hμ hsys').2 x hx (Ne.symm hn)
    linarith
  subst x'
  have heqs : s' = s := by
    ext j
    exact mul_right_cancel₀ (hx.2 j).ne' ((hsys'.2.2.1 j).trans (hsys.2.2.1 j).symm)
  have heqy : y' = y := by
    apply rank_transpose_injective A hrank
    have hh := hsys'.2.1
    rw [heqs] at hh
    exact sub_left_injective (hh.trans hsys.2.1.symm)
  exact ⟨rfl, heqy, heqs⟩
