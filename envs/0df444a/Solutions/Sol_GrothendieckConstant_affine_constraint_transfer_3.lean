-- Prove2me | solution 3 for GrothendieckConstant.affine_constraint_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:20:07.99401+00:00
-- url     : https://prove2.me/submissions/4fe88fbf-b979-40f8-a9ef-ffa89e4274f5

import Theorems.Thm_GrothendieckConstant_coeff_hermite_moments
import Theorems.Thm_GrothendieckConstant_exists_grothendieck_bound

/-!
# Transfer of the affine coefficient constraint

A finite family of Gaussian Hermite features turns the scalar hypothesis into a matrix
inequality for odd signs. Finite approximation and the definition of a Grothendieck
bound extend that inequality to odd maps into a Euclidean ball. In dimension `d` we
test it with the coordinate vector times a Gaussian density ratio of variance
`d / (d + 1)`. Its linear energy tends to one and its cubic energy tends to zero.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology GrothendieckConstant
open scoped BigOperators

namespace AffineTransferProof

/- The padding and boundedness arguments are from the Prove2Me proofs of
`exists_grothendieck_bound` (Nickrobbins95, f260128e-39ad-469d-96d6-7bf32941862c)
and `pi_div_two_le_grothendieckConst` (ffaa9038-c1b0-4f89-a992-ec0ecc1ccaff). -/
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

theorem pad_mem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {ι : Type} [Fintype ι]
    (f : Fin m → ι → ℝ) (g : Fin n → ι → ℝ)
    (hf : ∀ i, ∑ k, f i k ^ 2 ≤ 1) (hg : ∀ j, ∑ k, g j k ^ 2 ≤ 1) :
    ∑ i, ∑ j, A i j * ∑ k, f i k * g j k ∈ sdpSet A := by
  classical
  let F : Fin m → ι ⊕ (Fin m ⊕ Fin n) → ℝ := fun i =>
    Sum.elim (f i) (Sum.elim (fun i' => if i' = i then √(1 - ∑ k, f i k ^ 2) else 0) (fun _ => 0))
  let G : Fin n → ι ⊕ (Fin m ⊕ Fin n) → ℝ := fun j =>
    Sum.elim (g j) (Sum.elim (fun _ => 0) (fun j' => if j' = j then √(1 - ∑ k, g j k ^ 2) else 0))
  have hF : ∀ i, ∑ t, F i t ^ 2 = 1 := by
    intro i
    have h0 : 0 ≤ 1 - ∑ k, f i k ^ 2 := by linarith [hf i]
    simp only [F, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp [Real.sq_sqrt h0]
  have hG : ∀ j, ∑ t, G j t ^ 2 = 1 := by
    intro j
    have h0 : 0 ≤ 1 - ∑ k, g j k ^ 2 := by linarith [hg j]
    simp only [G, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp [Real.sq_sqrt h0]
  have hFG : ∀ i j, ∑ t, F i t * G j t = ∑ k, f i k * g j k := by
    intro i j
    simp [F, G, Fintype.sum_sum_type]
  let e := Fintype.equivFin (ι ⊕ (Fin m ⊕ Fin n))
  refine ⟨Fintype.card (ι ⊕ (Fin m ⊕ Fin n)),
    fun i => WithLp.toLp 2 (fun k => F i (e.symm k)),
    fun j => WithLp.toLp 2 (fun k => G j (e.symm k)), ?_, ?_, ?_⟩
  · intro i
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [e.symm.sum_comp (fun t => F i t ^ 2), hF i, Real.sqrt_one]
  · intro j
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [e.symm.sum_comp (fun t => G j t ^ 2), hG j, Real.sqrt_one]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [EuclideanSpace.inner_toLp_toLp, ← hFG i j]
    simp only [dotProduct, star_trivial]
    rw [← e.symm.sum_comp (fun t => F i t * G j t)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

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

abbrev X (d : ℕ) := Fin d → ℝ

/-- The signed Gram matrix of a finite list of real features. -/
noncomputable def featureMatrix {m : ℕ} {R : Type} [Fintype R]
    (w : R → ℝ) (b : Fin m → R → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => ∑ r, w r * b i r * b j r

lemma featureMatrix_bilin {m : ℕ} {R : Type} [Fintype R]
    (w : R → ℝ) (b : Fin m → R → ℝ) (u v : Fin m → ℝ) :
    ∑ i, ∑ j, featureMatrix w b i j * u i * v j =
      ∑ r, w r * (∑ i, u i * b i r) * (∑ j, v j * b j r) := by
  classical
  simp only [featureMatrix, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma vector_score {m a : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → Fin a → ℝ) :
    ∑ i, ∑ j, A i j * ∑ l, u i l * u j l =
      ∑ l, ∑ i, ∑ j, A i j * u i l * u j l := by
  simp only [Finset.mul_sum, mul_assoc]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

lemma pm_mul {s t : ℝ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    s * t = 1 ∨ s * t = -1 := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num

lemma pm_abs {s : ℝ} (hs : s = 1 ∨ s = -1) : |s| = 1 := by
  rcases hs with rfl | rfl <;> norm_num

end AffineTransferProof

open MeasureTheory ProbabilityTheory Real Filter Topology GrothendieckConstant
open scoped BigOperators
namespace AffineTransferProof

/-- The moment of a feature on each fiber of a finite measurement. -/
noncomputable def cell {d m : ℕ} (p : X d → Fin m) (sg t : X d → ℝ) (i : Fin m) : ℝ :=
  ∫ x, if p x = i then sg x * t x else 0

lemma linear_moment {d m : ℕ} (p : X d → Fin m) (hp : Measurable p)
    (sg t : X d → ℝ) (hsgt : Integrable (fun x => sg x * t x)) (u : Fin m → ℝ) :
    (∫ x, (sg x * u (p x)) * t x) = ∑ i, u i * cell p sg t i := by
  classical
  have hi (i : Fin m) : Integrable (fun x => if p x = i then sg x * t x else 0) :=
    by
      refine (hsgt.indicator (hp (measurableSet_singleton i))).congr (ae_of_all _ fun x => ?_)
      by_cases hx : p x = i <;> simp [hx]
  simp only [cell, ← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ => (hi i).const_mul (u i))]
  apply integral_congr_ae
  filter_upwards with x
  simp [mul_ite, ← mul_assoc, mul_comm (sg x) (u (p x))]

lemma signed_integrable {d : ℕ} {sg t : X d → ℝ} (hm : Measurable sg)
    (hs : ∀ x, sg x = 1 ∨ sg x = -1) (ht : Integrable t) :
    Integrable (fun x => sg x * t x) := by
  refine ht.norm.mono' (hm.aestronglyMeasurable.mul ht.aestronglyMeasurable) ?_
  filter_upwards with x
  simp [Real.norm_eq_abs, pm_abs (hs x)]

/-- Apply the defining matrix inequality for K to a finite measurement on Gaussian space. -/
lemma finite_vector_bound {R : Type} [Fintype R] {d m a : ℕ} (weight : R → ℝ)
    (T : R → X d → ℝ) (hT : ∀ r, Integrable (T r)) (C K : ℝ)
    (hK : IsGrothendieckBound K)
    (hsign : ∀ S : KrivineScheme d,
      ∑ r, weight r * (∫ x, S.f x * T r x) * (∫ x, S.g x * T r x) ≤ C)
    (p : X d → Fin m) (hp : Measurable p) (hpEven : ∀ᵐ x, p (-x) = p x)
    (sg : X d → ℝ) (hsg : Measurable sg) (hpm : ∀ x, sg x = 1 ∨ sg x = -1)
    (hodd : ∀ᵐ x, sg (-x) = -sg x) (u : Fin m → Fin a → ℝ)
    (hu : ∀ i, ∑ l, u i l ^ 2 ≤ 1) :
    ∑ l, ∑ r, weight r * (∫ x, (sg x * u (p x) l) * T r x) ^ 2 ≤ K * C := by
  classical
  let b (i : Fin m) (r : R) := cell p sg (T r) i
  let A := featureMatrix weight b
  have hmom (r : R) := linear_moment p hp sg (T r) (signed_integrable hsg hpm (hT r))
  have hopt : optValue A ≤ C := by
    apply csSup_le
    · exact ⟨_, fun _ => 1, fun _ => 1, fun _ => Or.inl rfl, fun _ => Or.inl rfl, rfl⟩
    rintro s ⟨v, w, hv, hw, rfl⟩
    let S : KrivineScheme d := {
      f := fun x => sg x * v (p x)
      g := fun x => sg x * w (p x)
      measurable_f := hsg.mul ((measurable_of_finite v).comp hp)
      measurable_g := hsg.mul ((measurable_of_finite w).comp hp)
      f_sign := fun x => pm_mul (hpm x) (hv _)
      g_sign := fun x => pm_mul (hpm x) (hw _)
      f_odd := by filter_upwards [hodd, hpEven] with x hx hpx; simp [hx, hpx]
      g_odd := by filter_upwards [hodd, hpEven] with x hx hpx; simp [hx, hpx] }
    rw [featureMatrix_bilin]
    simpa only [S, hmom, b] using hsign S
  have hval := le_csSup (sdpSet_bdd A) (pad_mem A u u hu hu)
  have hnonneg : 0 ≤ K := le_trans zero_le_one (one_le_of_isGrothendieckBound hK)
  have hbound := hval.trans ((hK m m A).trans (mul_le_mul_of_nonneg_left hopt hnonneg))
  rw [vector_score] at hbound
  have heq (l : Fin a) := featureMatrix_bilin weight b (fun i => u i l) (fun i => u i l)
  change (∑ l, ∑ i, ∑ j, featureMatrix weight b i j * u i l * u j l) ≤ K * C at hbound
  simp_rw [heq] at hbound
  have hi (l : Fin a) (r : R) := hmom r (fun i => u i l)
  simp_rw [hi, sq]
  simpa only [b, mul_assoc] using hbound

lemma coordinate_abs_le {a : ℕ} {v : Fin a → ℝ} (hv : ∑ l, v l ^ 2 ≤ 1) (l : Fin a) :
    |v l| ≤ 1 := by
  have h := Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ l)
  rw [abs_le]; constructor <;> nlinarith

/-- Bounded odd vector strategies inherit the finite Gram inequality by simple approximation. -/
lemma lift_vector_bound {R : Type} [Fintype R] {d a : ℕ} (hd : 0 < d) (weight : R → ℝ)
    (T : R → X d → ℝ) (hT : ∀ r, Integrable (T r)) (C K : ℝ) (hK : IsGrothendieckBound K)
    (hsign : ∀ S : KrivineScheme d,
      ∑ r, weight r * (∫ x, S.f x * T r x) * (∫ x, S.g x * T r x) ≤ C)
    (v : X d → X a) (hv : Measurable v) (hb : ∀ x, ∑ l, v x l ^ 2 ≤ 1)
    (ho : ∀ x, v (-x) = -v x) :
    ∑ l, ∑ r, weight r * (∫ x, v x l * T r x) ^ 2 ≤ K * C := by
  classical
  let S := halfspaceScheme d hd
  let f (x : X d) : X a := S.f x • v x
  have hf : Measurable f := S.measurable_f.smul hv
  have hfe : ∀ᵐ x, f (-x) = f x := by
    filter_upwards [S.f_odd] with x hx
    simp [f, hx, ho]
  let B : Set (X a) := {w | ∑ l, w l ^ 2 ≤ 1}
  have h0 : (0 : X a) ∈ B := by simp [B]
  have hfB (x : X d) : f x ∈ B := by
    rcases S.f_sign x with h | h <;> simpa [B, f, h] using hb x
  let q (n : ℕ) := SimpleFunc.approxOn id measurable_id B 0 h0 n
  let u (n : ℕ) (x : X d) (l : Fin a) := S.f x * q n (f x) l
  have hqB n x : q n x ∈ B := SimpleFunc.approxOn_mem ..
  have hpoint (x : X d) (l : Fin a) : Tendsto (fun n => u n x l) atTop (𝓝 (v x l)) := by
    have hh : Tendsto (fun n => q n (f x)) atTop (𝓝 (f x)) :=
      SimpleFunc.tendsto_approxOn measurable_id h0 (subset_closure (hfB x))
    have hlim := (tendsto_pi_nhds.mp hh l).const_mul (S.f x)
    rcases S.f_sign x with h | h <;> simpa [u, f, h] using hlim
  have hmom (l : Fin a) (r : R) :
      Tendsto (fun n => ∫ x, u n x l * T r x) atTop (𝓝 (∫ x, v x l * T r x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖T r x‖)
    · intro n
      exact (S.measurable_f.mul ((measurable_pi_apply l).comp ((q n).measurable.comp hf))).aestronglyMeasurable.mul (hT r).aestronglyMeasurable
    · exact (hT r).norm
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have h := coordinate_abs_le (hqB n (f x)) l
      have h' : |u n x l| ≤ 1 := by simpa [u, abs_mul, pm_abs (S.f_sign x)] using h
      simpa using mul_le_mul_of_nonneg_right h' (abs_nonneg (T r x))
    · filter_upwards with x using (hpoint x l).mul_const (T r x)
  apply le_of_tendsto' (tendsto_finsetSum _ fun l _ =>
    tendsto_finsetSum _ fun r _ => ((hmom l r).pow 2).const_mul (weight r))
  intro n
  let V := (q n).range
  let e := Fintype.equivFin (↑V)
  let p (x : X d) := e ⟨q n (f x), (q n).mem_range_self _⟩
  have hp : Measurable p := (measurable_of_finite e).comp (((q n).measurable.comp hf ).subtype_mk)
  have hpe : ∀ᵐ x, p (-x) = p x := by
    filter_upwards [hfe] with x hx
    simp [p, hx]
  let U (i : Fin (Fintype.card (↑V))) : X a := (e.symm i).val
  have hU (i) : ∑ l, U i l ^ 2 ≤ 1 := by
    obtain ⟨x, hx⟩ := SimpleFunc.mem_range.mp (e.symm i).property
    change (e.symm i).val ∈ B
    rw [← hx]
    exact hqB n x
  simpa only [u, U, p, Equiv.symm_apply_apply] using
    finite_vector_bound weight T hT C K hK hsign p hp hpe S.f S.measurable_f S.f_sign S.f_odd U hU

end AffineTransferProof

open MeasureTheory ProbabilityTheory Real Filter Topology GrothendieckConstant
open scoped BigOperators NNReal ENNReal
namespace AffineTransferProof

noncomputable def density {d : ℕ} (v : ℝ≥0) (x : X d) : ℝ := ∏ i, gaussianPDFReal 0 v (x i)
noncomputable def rawMoment (v : ℝ≥0) (n : ℕ) : ℝ := ∫ t : ℝ, t ^ n * gaussianPDFReal 0 v t

lemma rawMoment_eq {v : ℝ≥0} (hv : v ≠ 0) (n : ℕ) :
    rawMoment v n = ∫ t : ℝ, t ^ n ∂gaussianReal 0 v := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp [rawMoment, smul_eq_mul, mul_comm]

lemma integrable_rawMoment {v : ℝ≥0} (hv : v ≠ 0) (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n * gaussianPDFReal 0 v t) := by
  have h : Integrable (fun t : ℝ => t ^ n) (gaussianReal 0 v) := by
    simpa using integrable_pow_of_mem_interior_integrableExpSet (X := id) (μ := gaussianReal 0 v) (by simp) n
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  simpa only [toReal_gaussianPDF, smul_eq_mul, mul_comm] using h

lemma rawMoment_zero {v : ℝ≥0} (hv : v ≠ 0) : rawMoment v 0 = 1 := by simp [rawMoment_eq hv]
lemma rawMoment_one {v : ℝ≥0} (hv : v ≠ 0) : rawMoment v 1 = 0 := by simp [rawMoment_eq hv]
lemma rawMoment_two {v : ℝ≥0} (hv : v ≠ 0) : rawMoment v 2 = v := by
  rw [rawMoment_eq hv]
  have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa using h

lemma rawMoment_three_four {v : ℝ≥0} (hv : v ≠ 0) :
    rawMoment v 3 = 0 ∧ rawMoment v 4 = 3 * (v : ℝ)^2 := by
  let c := (v : ℝ)
  let E := fun t : ℝ => exp (c * t^2 / 2)
  have dE (t : ℝ) : HasDerivAt E (c*t*E t) t := by
    convert ((((hasDerivAt_id t).pow 2).const_mul c).div_const 2).exp using 1 <;>
      first | rfl | (simp [E]; ring)
  have h1 : deriv E = fun t => c*t*E t := funext fun t => (dE t).deriv
  have h2 : deriv (fun t => c*t*E t) = fun t => (c+c^2*t^2)*E t := by
    funext t; convert (((hasDerivAt_id t).const_mul c).mul (dE t)).deriv using 1 <;>
      first | rfl | (simp; ring)
  have h3 : deriv (fun t => (c+c^2*t^2)*E t) = fun t => (3*c^2*t+c^3*t^3)*E t := by
    funext t; convert (((((hasDerivAt_id t).pow 2).const_mul (c^2)).const_add c).mul (dE t)).deriv using 1 <;>
      first | rfl | (simp; ring)
  have h4 : deriv (fun t => (3*c^2*t+c^3*t^3)*E t) =
      fun t => (3*c^2+6*c^3*t^2+c^4*t^4)*E t := by
    funext t; convert ((((hasDerivAt_id t).const_mul (3*c^2)).add
      (((hasDerivAt_id t).pow 3).const_mul (c^3))).mul (dE t)).deriv using 1 <;>
      first | rfl | (simp; ring)
  have hm (n : ℕ) : rawMoment v n = iteratedDeriv n E 0 := by
    rw [rawMoment_eq hv]
    have ht := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) n
    simpa [mgf_fun_id_gaussianReal, Pi.pow_apply, E, c] using ht.symm
  rw [hm, hm]
  constructor
  · rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero, h1, h2, h3]; simp
  · rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero, h1, h2, h3, h4]; simp [E,c]

/-- A product of coordinates, with repetitions encoded by a list. -/
def mon {d : ℕ} (L : List (Fin d)) (x : X d) : ℝ := (L.map x).prod

lemma mon_as_prod {d : ℕ} (L : List (Fin d)) (x : X d) :
    mon L x = ∏ i, x i ^ L.count i := by
  induction L with
  | nil => simp [mon]
  | cons j L ih =>
    simp only [List.count_cons, pow_add, Finset.prod_mul_distrib]
    rw [show mon (j :: L) x = x j * mon L x by simp [mon], ih]
    simp [apply_ite, mul_comm]

lemma mon_density_prod {d : ℕ} (v : ℝ≥0) (L : List (Fin d)) (x : X d) :
    mon L x * density v x = ∏ i, x i ^ L.count i * gaussianPDFReal 0 v (x i) := by
  rw [mon_as_prod, Finset.prod_mul_distrib]; rfl

lemma integrable_mon {d : ℕ} {v : ℝ≥0} (hv : v ≠ 0) (L : List (Fin d)) :
    Integrable (fun x : X d => mon L x * density v x) := by
  simp_rw [mon_density_prod]; rw [volume_pi]
  exact Integrable.fintype_prod (f := fun i t => t ^ L.count i * gaussianPDFReal 0 v t) fun i => integrable_rawMoment hv _

lemma integral_mon {d : ℕ} {v : ℝ≥0} (hv : v ≠ 0) (L : List (Fin d)) :
    (∫ x : X d, mon L x * density v x) = ∏ i ∈ L.toFinset, rawMoment v (L.count i) := by
  simp_rw [mon_density_prod]; rw [volume_pi, integral_fintype_prod_eq_prod (fun i t => t ^ L.count i * gaussianPDFReal 0 v t)]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [List.mem_toFinset] at hi
  simp [List.count_eq_zero_of_not_mem hi, rawMoment_zero hv]

lemma moment_two {d : ℕ} {v : ℝ≥0} (hv : v ≠ 0) (i j : Fin d) :
    (∫ x : X d, x i * x j * density v x) = if i = j then (v : ℝ) else 0 := by
  have h := integral_mon hv [i,j]
  by_cases hij : i = j
  · subst j; simpa [mon, rawMoment_two hv] using h
  · simpa [mon, hij, Ne.symm hij, List.count_cons, rawMoment_one hv] using h

/-- Wick's fourth-moment identity for the product Gaussian. -/
lemma moment_four {d : ℕ} {v : ℝ≥0} (hv : v ≠ 0) (a i j l : Fin d) :
    (∫ x : X d, x a * x i * x j * x l * density v x) = (v : ℝ)^2 *
      ((if a=i ∧ j=l then 1 else 0) + (if a=j ∧ i=l then 1 else 0) + (if a=l ∧ i=j then 1 else 0)) := by
  have h := integral_mon hv [a,i,j,l]
  have h3 := (rawMoment_three_four hv).1
  have h4 := (rawMoment_three_four hv).2
  by_cases h1 : a=i <;> by_cases h2 : a=j <;> by_cases h3' : a=l <;>
    by_cases h5 : i=j <;> by_cases h6 : i=l <;> by_cases h7 : j=l <;>
    (try have e1 := Ne.symm h1) <;> (try have e2 := Ne.symm h2) <;> (try have e3 := Ne.symm h3') <;>
    (try have e5 := Ne.symm h5) <;> (try have e6 := Ne.symm h6) <;> (try have e7 := Ne.symm h7) <;>
    subst_vars <;> first | contradiction | (simp_all [mon, List.count_cons, rawMoment_one hv, rawMoment_two hv, mul_assoc, sq] <;> linarith)

end AffineTransferProof

open MeasureTheory ProbabilityTheory Real Filter Topology GrothendieckConstant
open scoped BigOperators NNReal ENNReal
namespace AffineTransferProof

noncomputable def tiltedVar (d : ℕ) : ℝ≥0 := ⟨(d : ℝ)/(d+1), by positivity⟩
@[simp] lemma coe_tiltedVar (d : ℕ) : (tiltedVar d : ℝ) = (d : ℝ)/(d+1) := rfl
lemma tilted_ne {d : ℕ} (hd : 0 < d) : tiltedVar d ≠ 0 := by
  have : (0 : ℝ) < (d : ℝ) / (d+1) := by positivity
  exact ne_of_gt (show 0 < tiltedVar d from this)

noncomputable def damp {d : ℕ} (x : X d) : ℝ :=
  (√(1+1/(d:ℝ)))^d * exp (-(∑ i, x i ^ 2)/(2*d))
noncomputable def testVec {d : ℕ} (x : X d) (i : Fin d) : ℝ :=
  (√(d:ℝ))⁻¹ * x i * damp x

lemma measurable_testVec (d : ℕ) : Measurable (@testVec d) := by
  unfold testVec damp; fun_prop

lemma testVec_neg {d : ℕ} (x : X d) : testVec (-x) = -testVec x := by
  funext i; simp [testVec, damp]

lemma testVec_bound {d : ℕ} (hd : 0 < d) (x : X d) : ∑ i, testVec x i ^ 2 ≤ 1 := by
  let D : ℝ := d
  let Q : ℝ := ∑ i, x i ^ 2
  have hD : 0 < D := Nat.cast_pos.mpr hd
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hp : (1 + 1/D)^d ≤ exp 1 := calc
    (1+1/D)^d ≤ (exp (1/D))^d := by
      gcongr; linarith [Real.add_one_le_exp (1/D)]
    _ = exp 1 := by rw [← Real.exp_nat_mul]; congr 1; change D * (1/D) = 1; field_simp
  have hsum : (∑ i, testVec x i ^ 2) = ((1+1/D)^d * exp (-(Q/D))) * (Q/D) := by
    simp only [testVec, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg d), ← Finset.sum_mul, ← Finset.mul_sum]
    change (D⁻¹ * Q) * ((√(1+1/D))^d * exp (-Q/(2*D)))^2 = _
    rw [mul_pow, pow_right_comm, Real.sq_sqrt (by positivity : 0 ≤ 1+1/D), ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-Q/(2*D)) = -(Q/D) by ring]; ring
  rw [hsum]
  calc
    _ ≤ (exp 1 * exp (-(Q/D))) * (Q/D) := by gcongr
    _ = exp (1-Q/D) * (Q/D) := by rw [← Real.exp_add]; rfl
    _ ≤ exp (1-Q/D) * exp (Q/D-1) := by
      gcongr; linarith [Real.add_one_le_exp (Q/D-1)]
    _ = 1 := by rw [← Real.exp_add]; ring_nf; simp

lemma scalar_tilt {d : ℕ} (hd : 0 < d) (x : ℝ) :
    (√(1+1/(d:ℝ)) * exp (-(x^2)/(2*d))) * gaussianPDFReal 0 1 x =
    gaussianPDFReal 0 (tiltedVar d) x := by
  let D : ℝ := d
  have hD : 0 < D := Nat.cast_pos.mpr hd
  have hv : 0 < D/(D+1) := by positivity
  have hs : √(1+1/D) * √(D/(D+1)) = 1 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 1+1/D)]
    convert Real.sqrt_one using 2; field_simp
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, coe_tiltedVar]
  change (√(1+1/D) * exp (-(x^2)/(2*D))) * ((√(2*π))⁻¹ * exp (-(x^2)/2)) =
    (√(2*π*(D/(D+1))))⁻¹ * exp (-(x^2)/(2*(D/(D+1))))
  rw [show -(x^2)/(2*(D/(D+1))) = -(x^2)/(2*D) + -(x^2)/2 by field_simp; ring, Real.exp_add]
  rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*π), mul_inv_rev]
  rw [show √(1+1/D) = (√(D/(D+1)))⁻¹ from (eq_inv_of_mul_eq_one_left hs)]
  ring

lemma damp_density {d : ℕ} (hd : 0 < d) (x : X d) :
    damp x * density 1 x = density (tiltedVar d) x := by
  have eqd : damp x = ∏ i, (√(1+1/(d:ℝ)) * exp (-(x i^2)/(2*d))) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_div, Finset.sum_neg_distrib]
    simp [damp]
  rw [eqd, density, ← Finset.prod_mul_distrib]; unfold density
  exact Finset.prod_congr rfl fun i _ => scalar_tilt hd _

/-- Contract the three possible pairings of a fourth Gaussian moment. -/
def pairings {d : ℕ} (a i j l : Fin d) : ℝ :=
  (if a=i ∧ j=l then 1 else 0) + (if a=j ∧ i=l then 1 else 0) + (if a=l ∧ i=j then 1 else 0)

noncomputable def herm {d : ℕ} (x : X d) (i j l : Fin d) : ℝ :=
  x i*x j*x l - (if i=j then x l else 0) - (if i=l then x j else 0) - (if j=l then x i else 0)

lemma integrable_coord {d : ℕ} {v : ℝ≥0} (hv : v ≠ 0) (i : Fin d) :
    Integrable (fun x : X d => x i * density v x) := by simpa [mon] using integrable_mon hv [i]

lemma integrable_sub_fun {d : ℕ} {f g : X d → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => f x - g x) := hf.sub hg

lemma integrable_herm {d : ℕ} {v : ℝ≥0} (hv : v ≠ 0) (i j l : Fin d) :
    Integrable (fun x : X d => herm x i j l * density v x) := by
  have h3 : Integrable (fun x : X d => x i*x j*x l * density v x) := by
    simpa [mon, mul_assoc] using integrable_mon hv [i,j,l]
  have hg (P : Prop) [Decidable P] (a : Fin d) : Integrable (fun x : X d => (if P then x a else 0) * density v x) := by
    split <;> simp [integrable_coord hv]
  simpa only [herm, sub_mul, Pi.sub_apply] using integrable_sub_fun (integrable_sub_fun (integrable_sub_fun h3 (hg (i=j) l)) (hg (i=l) j)) (hg (j=l) i)

lemma test_first {d : ℕ} (hd : 0 < d) (a i : Fin d) :
    (∫ x : X d, testVec x a * (x i * density 1 x)) =
      (√(d:ℝ))⁻¹ * (if a=i then (tiltedVar d : ℝ) else 0) := by
  have hp (x : X d) : testVec x a * (x i * density 1 x) =
       (√(d:ℝ))⁻¹ * (x a * x i * density (tiltedVar d) x) := by
    rw [← damp_density hd]; unfold testVec; ring
  simp_rw [hp]; rw [integral_const_mul, moment_two (tilted_ne hd)]

lemma test_third {d : ℕ} (hd : 0 < d) (a i j l : Fin d) :
    (∫ x : X d, testVec x a * (herm x i j l * density 1 x)) =
      (√(d:ℝ))⁻¹ * (((tiltedVar d : ℝ)^2 - tiltedVar d) * pairings a i j l) := by
  let v := tiltedVar d
  have hv : v ≠ 0 := tilted_ne hd
  have hp (x : X d) : testVec x a * (herm x i j l * density 1 x) =
      (√(d:ℝ))⁻¹ * (x a * herm x i j l * density v x) := by
    rw [← damp_density hd]; unfold testVec; ring
  simp_rw [hp]; rw [integral_const_mul]; congr 1
  have H4 : Integrable (fun x : X d => x a*x i*x j*x l*density v x) := by
    simpa [mon, mul_assoc] using integrable_mon hv [a,i,j,l]
  have H2 (k : Fin d) : Integrable (fun x : X d => x a*x k*density v x) := by
    simpa [mon] using integrable_mon hv [a,k]
  have HG (P : Prop) [Decidable P] (k : Fin d) : Integrable (fun x : X d => if P then x a*x k*density v x else 0) := by
    by_cases h : P <;> simp [h, H2]
  have IG (P : Prop) [Decidable P] (k : Fin d) :
      (∫ x : X d, if P then x a*x k*density v x else 0) = if a=k ∧ P then (v:ℝ) else 0 := by
    by_cases h : P <;> simp [h, moment_two hv]
  have expand (x : X d) : x a * herm x i j l * density v x =
      x a*x i*x j*x l*density v x - (if i=j then x a*x l*density v x else 0) -
      (if i=l then x a*x j*density v x else 0) - (if j=l then x a*x i*density v x else 0) := by
    simp only [herm, mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]; ring
  simp_rw [expand]
  rw [integral_sub (integrable_sub_fun (integrable_sub_fun H4 (HG (i=j) l)) (HG (i=l) j)) (HG (j=l) i),
    integral_sub (integrable_sub_fun H4 (HG (i=j) l)) (HG (i=l) j), integral_sub H4 (HG (i=j) l),
    moment_four hv, IG, IG, IG]
  unfold pairings
  change _ = (((v:ℝ)^2 - v) * _)
  split_ifs <;> ring

end AffineTransferProof

open MeasureTheory ProbabilityTheory Real Filter Topology GrothendieckConstant
open scoped BigOperators NNReal
namespace AffineTransferProof

abbrev Feat (d : ℕ) := Fin d ⊕ (Fin d × Fin d × Fin d)

noncomputable def weights (d : ℕ) (lam : ℝ) : Feat d → ℝ :=
  Sum.elim (fun _ => (1+lam)*(π/2)) (fun _ => -(π/12))

noncomputable def features (d : ℕ) : Feat d → X d → ℝ :=
  Sum.elim (fun i x => x i * density 1 x)
    (fun t x => herm x t.1 t.2.1 t.2.2 * density 1 x)

lemma split_features {d : ℕ} (lam : ℝ) (B : Feat d → ℝ) :
    (∑ r, weights d lam r * B r) =
    (1+lam)*(π/2)*(∑ i, B (.inl i)) -
    (π/12)*(∑ i, ∑ j, ∑ l, B (.inr (i,j,l))) := by
  simp [weights, Fintype.sum_prod_type, Finset.mul_sum, sub_eq_add_neg]

lemma sign_score {d : ℕ} {lam : ℝ} (S : KrivineScheme d)
    (hc : (1+lam)*coeffLinear S - (lam+5/6) ≤ coeffCubic S) :
    ∑ r, weights d lam r * (∫ x, S.f x * features d r x) *
      (∫ x, S.g x * features d r x) ≤ lam+5/6 := by
  rw [(coeff_hermite_moments d S).1, (coeff_hermite_moments d S).2] at hc
  simp only [mul_assoc]
  rw [split_features]
  simp only [features, Sum.elim_inl, Sum.elim_inr, density, herm, mul_assoc] at hc ⊢
  linarith only [hc]

lemma first_energy {d : ℕ} (hd : 0 < d) :
    (∑ a : Fin d, ∑ i : Fin d, (∫ x, testVec x a * (x i * density 1 x))^2) =
      (tiltedVar d : ℝ)^2 := by
  simp_rw [test_first hd]
  have h (a : Fin d) : (∑ i : Fin d, ((√(d:ℝ))⁻¹ * (if a=i then (tiltedVar d : ℝ) else 0))^2) =
      ((√(d:ℝ))⁻¹ * (tiltedVar d : ℝ))^2 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba; simp [Ne.symm hba]
    · simp
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  have hD : (0:ℝ)<d := Nat.cast_pos.mpr hd
  field_simp

lemma total_pairings (d : ℕ) :
    (∑ a : Fin d, ∑ i : Fin d, ∑ j : Fin d, ∑ l : Fin d, pairings a i j l) = 3*(d:ℝ)^2 := by
  classical
  simp [pairings, ite_and, Finset.sum_add_distrib, Finset.sum_ite_irrel]
  ring

lemma pairing_square {d : ℕ} (a i j l : Fin d) :
    pairings a i j l ^ 2 ≤ 3 * pairings a i j l := by
  unfold pairings
  split_ifs <;> norm_num

lemma total_pairing_sq (d : ℕ) :
    (∑ a : Fin d, ∑ i : Fin d, ∑ j : Fin d, ∑ l : Fin d, pairings a i j l ^ 2) ≤ 9*(d:ℝ)^2 := calc
  _ ≤ ∑ a : Fin d, ∑ i : Fin d, ∑ j : Fin d, ∑ l : Fin d, 3*pairings a i j l := by
    gcongr with a _ i _ j _ l _
    exact pairing_square a i j l
  _ = _ := by simp only [← Finset.mul_sum, total_pairings]; ring

lemma cubic_energy {d : ℕ} (hd : 0 < d) :
    (∑ a : Fin d, ∑ i : Fin d, ∑ j : Fin d, ∑ l : Fin d,
      (∫ x, testVec x a * (herm x i j l * density 1 x))^2) ≤ 9/((d:ℝ)+1) := by
  let b : ℝ := (√(d:ℝ))⁻¹ * ((tiltedVar d : ℝ)^2 - tiltedVar d)
  have hm (a i j l : Fin d) :
      (∫ x, testVec x a * (herm x i j l * density 1 x))^2 = b^2 * (pairings a i j l)^2 := by
    rw [test_third hd]; dsimp only [b]; ring
  simp_rw [hm]
  simp only [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (total_pairing_sq d) (sq_nonneg b)).trans
  have hD : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have h1 : (0:ℝ)<d+1 := by positivity
  simp only [b, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg d), coe_tiltedVar]
  field_simp
  nlinarith [sq_nonneg (d:ℝ)]

lemma dimension_bound {d : ℕ} (hd : 0 < d) (lam K : ℝ) (hK : IsGrothendieckBound K)
    (hc : ∀ S : KrivineScheme d, (1+lam)*coeffLinear S - (lam+5/6) ≤ coeffCubic S) :
    (1+lam)*(π/2)*((d:ℝ)/(d+1))^2 - (π/12)*(9/((d:ℝ)+1)) ≤ K*(lam+5/6) := by
  have hT (r : Feat d) : Integrable (features d r) := by
    rcases r with i | ⟨i,j,l⟩
    · exact integrable_coord one_ne_zero i
    · exact integrable_herm one_ne_zero i j l
  have h := lift_vector_bound hd (weights d lam) (features d) hT (lam+5/6) K hK
    (fun S => sign_score S (hc S)) testVec (measurable_testVec d) (testVec_bound hd) testVec_neg
  simp_rw [split_features] at h
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, features, Sum.elim_inl, Sum.elim_inr,
    first_energy hd, coe_tiltedVar] at h
  linarith only [h, mul_le_mul_of_nonneg_left (cubic_energy hd) (show 0 ≤ π/12 by positivity)]

end AffineTransferProof

open AffineTransferProof

theorem solution (lam : ℝ) (hlam : 1 / 2 ≤ lam)
    (hcon : ∀ (k : ℕ) (S : KrivineScheme k),
      (1 + lam) * coeffLinear S - (lam + 5 / 6) ≤ coeffCubic S) :
    Real.pi * (1 + lam) / (2 * (lam + 5 / 6)) ≤ grothendieckConst := by
  apply le_csInf (s := {K : ℝ | IsGrothendieckBound K}) exists_grothendieck_bound
  intro K hK
  have hs := ((tendsto_natCast_div_add_atTop (1:ℝ)).pow 2).const_mul ((1+lam)*(π/2))
  have ht : Tendsto (fun d : ℕ => 9/((d:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (9:ℝ)
  have hlim := hs.sub (ht.const_mul (π/12))
  have h : (1+lam)*(π/2) ≤ K*(lam+5/6) := by
    apply le_of_tendsto (by simpa only [one_pow, mul_one, mul_zero, sub_zero] using hlim)
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    exact dimension_bound hd lam K hK (hcon d)
  apply (div_le_iff₀ (by linarith : 0 < 2*(lam+5/6))).2
  linarith only [h]
