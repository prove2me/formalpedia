-- Prove2me | solution 1 for HighResODE.NAGSC.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T14:56:58.452958+00:00
-- url     : https://prove2.me/submissions/c62a6df4-b578-4d1c-9706-508868b3be2f

import Mathlib
import Definitions.Def_HighResODE_NAGSC_Setting

-- Complete module: NSProof/SharedBasics.lean
open scoped RealInnerProductSpace

-- Complete module: NSProof/ScalarSmooth.lean
namespace HighResODE.NAGSC.NSFresh

theorem scalar_descent (f f' : ℝ → ℝ) (L : ℝ) (hd : ∀ z, HasDerivAt f (f' z) z)
    (hL : ∀ a b, |f' a-f' b| ≤ L*|a-b|) (a b : ℝ) :
    f b ≤ f a + f' a*(b-a) + L/2*(b-a)^2 := by
  let q : ℝ → ℝ := fun z => f z - f a - f' a*(z-a) - L/2*(z-a)^2
  have hq (z : ℝ) : HasDerivAt q (f' z-f' a-L*(z-a)) z := by
    have h := (((hd z).sub_const (f a)).sub (((hasDerivAt_id z).sub_const a).const_mul (f' a))).sub
      ((((hasDerivAt_id z).sub_const a).pow 2).const_mul (L/2)) 
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hc : Continuous q := continuous_iff_continuousAt.mpr fun z => (hq z).continuousAt
  have hdiff : Differentiable ℝ q := fun z => (hq z).differentiableAt
  have hqa : q a = 0 := by simp [q]
  rcases le_total a b with hab | hba
  · have hm : AntitoneOn q (Set.Ici a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have haz : a ≤ z := (interior_subset hz)
      have h := (abs_le.mp (hL z a)).2
      rw [abs_of_nonneg (sub_nonneg.mpr haz)] at h
      linarith
    have h := hm (by simp) hab hab
    rw [hqa] at h
    dsimp [q] at h
    linarith
  · have hm : MonotoneOn q (Set.Iic a) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have hza : z ≤ a := (interior_subset (s := Set.Iic a) hz)
      have h := (abs_le.mp (hL z a)).1
      rw [abs_of_nonpos (sub_nonpos.mpr hza)] at h
      linarith
    have h := hm hba (by simp) hba
    rw [hqa] at h
    dsimp [q] at h
    linarith

end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/SmoothDescent.lean
open scoped RealInnerProductSpace
namespace HighResODE.NAGSC.NSFresh
variable {p : ℕ}
lemma smooth_descent (f : EuclideanSpace ℝ (Fin p) → ℝ) (L : ℝ)
    (hf : Differentiable ℝ f)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖)
    (x y : EuclideanSpace ℝ (Fin p)) :
    f y ≤ f x + inner ℝ (gradient f x) (y-x) + L/2*‖y-x‖^2 := by
  let d := y-x
  let g : ℝ → ℝ := fun t => f (x+t • d)
  let g' : ℝ → ℝ := fun t => inner ℝ (gradient f (x+t • d)) d
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    exact ((hf _).hasGradientAt.hasFDerivAt.comp_hasDerivAt t (hd t))
  have hl (s t : ℝ) : |g' s - g' t| ≤ (L*‖d‖^2)*|s-t| := by
    dsimp [g']
    rw [← inner_sub_left]
    calc
      |inner ℝ (gradient f (x+s • d)-gradient f (x+t • d)) d| ≤
          ‖gradient f (x+s • d)-gradient f (x+t • d)‖*‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L*‖(x+s • d)-(x+t • d)‖)*‖d‖ := mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg _)
      _ = (L*‖d‖^2)*|s-t| := by
        rw [show (x+s • d)-(x+t • d) = (s-t) • d by module]
        rw [norm_smul, Real.norm_eq_abs]
        ring
  have h := scalar_descent g g' (L*‖d‖^2) hg hl 0 1
  simp only [g, g', zero_smul, add_zero, one_smul, sub_zero, one_pow, mul_one] at h
  have he : x + (y-x) = y := by abel
  dsimp [d] at h
  rw [he] at h
  nlinarith [h]
end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/ObjectiveBounds.lean
namespace HighResODE.NAGSC.NSFresh
variable {n : ℕ} {f : E n → ℝ} {μ L : ℝ}
lemma gradient_min_zero (hf : IsS1 f μ L) (xs : E n) (hm : ∀ z, f xs ≤ f z) :
    gradient f xs = 0 := by
  have hl : IsLocalMin f xs := Filter.Eventually.of_forall hm
  apply (InnerProductSpace.toDual ℝ _).injective
  rw [← (hf.isF1.differentiable xs).hasGradientAt.hasFDerivAt.fderiv,
    hl.fderiv_eq_zero, map_zero]
lemma gap_lower (hf : IsS1 f μ L) (xs : E n) (hm : ∀ z, f xs ≤ f z) (x : E n) :
    μ/2*‖x-xs‖^2 ≤ f x-f xs := by
  have h := hf.strongly_convex xs x
  rw [gradient_min_zero hf xs hm, inner_zero_left, add_zero] at h
  linarith
lemma gap_upper (hf : IsS1 f μ L) (xs : E n) (hm : ∀ z, f xs ≤ f z) (x : E n) :
    f x-f xs ≤ L/2*‖x-xs‖^2 := by
  have h := smooth_descent f L hf.isF1.differentiable hf.isF1.lipschitz_gradient xs x
  rw [gradient_min_zero hf xs hm, inner_zero_left, add_zero] at h
  linarith
lemma descent_step (hf : IsS1 f μ L) (x : E n) {s : ℝ} (hs : 0 ≤ s) (hLs : L*s ≤ 1) :
    f (x-s • gradient f x) ≤ f x-s/2*‖gradient f x‖^2 := by
  have h := smooth_descent f L hf.isF1.differentiable hf.isF1.lipschitz_gradient x (x-s • gradient f x)
  rw [show x-s • gradient f x-x = -s • gradient f x by module] at h
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, neg_sq] at h
  nlinarith [sq_nonneg ‖gradient f x‖, mul_nonneg hs (sub_nonneg.mpr hLs)]
lemma gradient_gap (hf : IsS1 f μ L) (xs : E n) (hm : ∀ z, f xs ≤ f z) (x : E n) :
    ‖gradient f x‖^2 ≤ 2*L*(f x-f xs) := by
  have hL := hf.isF1.L_pos
  have h := descent_step hf x (s := 1/L) (by positivity) (by rw [mul_one_div_cancel hL.ne'])
  have hm' := hm (x-(1/L) • gradient f x)
  have he : (1/L)/2 = 1/(2*L) := by ring
  rw [he, one_div_mul_eq_div] at h
  have hh : ‖gradient f x‖^2/(2*L) ≤ f x-f xs := by linarith
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2*L)).mp hh
lemma gap_compare (hf : IsS1 f μ L) (xs : E n) (hm : ∀ z, f xs ≤ f z) (x y : E n) :
    f x-f xs ≤ 2*(f y-f xs)+L*‖x-y‖^2 := by
  have h := smooth_descent f L hf.isF1.differentiable hf.isF1.lipschitz_gradient y x
  have hi := real_inner_le_norm (gradient f y) (x-y)
  have hg := gradient_gap hf xs hm y
  have hs := sq_nonneg (‖gradient f y‖-L*‖x-y‖)
  have hL := hf.isF1.L_pos
  nlinarith
end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/RunCoordinates.lean
namespace HighResODE.NAGSC.NSFresh
variable {n : ℕ}
noncomputable def auxiliary (a : ℝ) (x y : ℕ → E n) (k : ℕ) : E n :=
  a⁻¹ • ((1+a) • x k-y k)
lemma auxiliary_relation {a : ℝ} (ha : a ≠ 0) (x y : ℕ → E n) (k : ℕ) :
    a • (auxiliary a x y k-x k) = x k-y k := by
  dsimp [auxiliary]
  match_scalars
  all_goals field_simp
  all_goals ring
lemma auxiliary_difference {a : ℝ} (ha : a ≠ 0) (ha1 : 1+a ≠ 0)
    (x y : ℕ → E n) (k : ℕ) :
    x k-y k = (a/(1+a)) • (auxiliary a x y k-y k) := by
  dsimp [auxiliary]
  match_scalars
  all_goals field_simp
  all_goals ring
lemma auxiliary_init {a : ℝ} (ha : a ≠ 0) (x y : ℕ → E n) (hi : y 0=x 0) :
    auxiliary a x y 0=x 0 := by
  dsimp [auxiliary]
  rw [hi]
  match_scalars
  all_goals field_simp
  all_goals ring
lemma auxiliary_step {f : E n → ℝ} {μ s a : ℝ} {x y : ℕ → E n}
    (hr : IsNAGSC f μ s x y) (ha : a ≠ 0) (ha1 : 1+a ≠ 0)
    (hμ : μ ≠ 0) (hsq : a^2=μ*s) (he : Real.sqrt (μ*s)=a) (k : ℕ) :
    auxiliary a x y (k+1) = (1-a) • auxiliary a x y k+a • x k-(a/μ) • gradient f (x k) := by
  dsimp [auxiliary]
  rw [hr.step_x k, he, hr.step_y k]
  match_scalars
  all_goals field_simp
  all_goals nlinarith [hsq]
end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/EnergyAlgebra.lean
namespace HighResODE.NAGSC.NSFresh
variable {n : ℕ}
lemma update_norm_identity (z x xs g : E n) (a μ : ℝ) (hμ : μ ≠ 0) :
    μ/2*‖(1-a) • z+a • x-(a/μ) • g-xs‖^2 =
      (1-a)*(μ/2*‖z-xs‖^2)+a*(μ/2*‖x-xs‖^2)
      -μ/2*a*(1-a)*‖z-x‖^2
      -a*inner ℝ g ((1-a) • z+a • x-xs)+a^2/(2*μ)*‖g‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm z x, real_inner_comm z xs, real_inner_comm z g,
    real_inner_comm x xs, real_inner_comm x g, real_inner_comm xs g]
  field_simp
  ring
lemma pairing_identity (z x y xs g : E n) (a : ℝ)
    (hrel : a • (z-x)=x-y) :
    (1-a)*inner ℝ g (y-x)+a*inner ℝ g (xs-x) =
      -a*inner ℝ g ((1-a) • z+a • x-xs) := by
  have hh := congrArg (fun v => inner ℝ g v) hrel
  simp only [real_inner_smul_right, inner_sub_right] at hh
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
  nlinarith [congrArg (fun t : ℝ => (1-a)*t) hh]
lemma energy_contract_algebra {f : E n → ℝ} {μ L a s : ℝ} (hf : IsS1 f μ L)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hsq : a^2=μ*s)
    (x y z xs : E n) (hrel : a • (z-x)=x-y)
    (hd : f (x-s • gradient f x) ≤ f x-s/2*‖gradient f x‖^2) :
    f (x-s • gradient f x)-f xs+
      μ/2*‖(1-a) • z+a • x-(a/μ) • gradient f x-xs‖^2 ≤
      (1-a)*(f y-f xs+μ/2*‖z-xs‖^2) := by
  have hμ := hf.mu_pos
  rw [update_norm_identity z x xs (gradient f x) a μ hf.mu_pos.ne']
  have h1 := mul_le_mul_of_nonneg_left (hf.strongly_convex x y) (sub_nonneg.mpr ha1)
  have h2 := mul_le_mul_of_nonneg_left (hf.strongly_convex x xs) ha0
  have hp := pairing_identity z x y xs (gradient f x) a hrel
  have hc : a^2/(2*μ)=s/2 := by
    rw [hsq]
    field_simp
  rw [hc]
  have hn1 : 0 ≤ (1-a)*(μ/2*‖y-x‖^2) := by positivity
  have hn2 : 0 ≤ μ/2*a*(1-a)*‖z-x‖^2 := by positivity
  rw [norm_sub_rev xs x] at h2
  nlinarith only [hd,h1,h2,hp,hn1,hn2]
end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/RunEnergy.lean
namespace HighResODE.NAGSC.NSFresh
variable {n : ℕ}
noncomputable def runEnergy (f : E n → ℝ) (μ a : ℝ) (xs : E n) (x y : ℕ → E n) (k : ℕ) : ℝ :=
  f (y k)-f xs+μ/2*‖auxiliary a x y k-xs‖^2
lemma run_energy_init {f : E n → ℝ} {μ L a : ℝ} (hf : IsS1 f μ L)
    (xs : E n) (hm : ∀ z, f xs ≤ f z) (x y : ℕ → E n)
    (ha : a ≠ 0) (hi : y 0=x 0) :
    runEnergy f μ a xs x y 0 ≤ L*‖x 0-xs‖^2 := by
  unfold runEnergy
  rw [auxiliary_init ha x y hi,hi]
  have h := gap_upper hf xs hm (x 0)
  have hmL := hf.mu_le_L
  nlinarith [sq_nonneg ‖x 0-xs‖]
lemma run_energy_step {f : E n → ℝ} {μ L a : ℝ} (hf : IsS1 f μ L)
    (xs : E n) (x y : ℕ → E n) (hr : IsNAGSC f μ (1/(4*L)) x y)
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hsq : a^2=μ*(1/(4*L)))
    (he : Real.sqrt (μ*(1/(4*L)))=a) (k : ℕ) :
    runEnergy f μ a xs x y (k+1) ≤ (1-a)*runEnergy f μ a xs x y k := by
  have hL := hf.isF1.L_pos
  have hLs : L*(1/(4*L)) ≤ 1 := by
    have hh : L*(1/(4*L)) = 1/4 := by field_simp
    rw [hh]
    norm_num
  have hd := descent_step hf (x k) (s := 1/(4*L)) (by positivity) hLs
  have h := energy_contract_algebra hf ha.le (by linarith) hsq
    (x k) (y k) (auxiliary a x y k) xs (auxiliary_relation ha.ne' x y k) hd
  unfold runEnergy
  rw [hr.step_y k, auxiliary_step hr ha.ne' (by positivity) hf.mu_pos.ne' hsq he k]
  exact h
end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/OutputBound.lean

namespace HighResODE.NAGSC.NSFresh

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem output_energy_bound {F : V → ℝ} {x y z xs : V} {μ L a : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (ha : 0 ≤ a)
    (hsq : a ^ 2 = μ / (4 * L))
    (hlower : μ / 2 * ‖y - xs‖ ^ 2 ≤ F y)
    (hupper : F x ≤ 2 * F y + L * ‖x - y‖ ^ 2)
    (hrel : x - y = (a / (1 + a)) • (z - y)) :
    F x ≤ 3 * (F y + μ / 2 * ‖z - xs‖ ^ 2) := by
  have hb : 0 < 1 + a := by positivity
  have hn : ‖z - y‖ ≤ ‖z - xs‖ + ‖xs - y‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (z - xs) (xs - y)
  have hdist : ‖z - y‖ ^ 2 ≤ 2 * (‖z - xs‖ ^ 2 + ‖y - xs‖ ^ 2) := by
    rw [norm_sub_rev xs y] at hn
    have hz := norm_nonneg (z - y)
    have hy := norm_nonneg (y - xs)
    have hzx := norm_nonneg (z - xs)
    nlinarith [sq_nonneg (‖z - xs‖ - ‖y - xs‖)]
  have hxy : ‖x - y‖ ^ 2 = (a / (1 + a)) ^ 2 * ‖z - y‖ ^ 2 := by
    rw [hrel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hb.le)]
    ring
  have hc : L * (a / (1 + a)) ^ 2 ≤ μ / 4 := by
    have hid : L * a ^ 2 = μ / 4 := by
      rw [hsq]
      field_simp
    rw [div_pow, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hb)).2
    nlinarith [sq_nonneg a]
  have hnorm : L * ‖x - y‖ ^ 2 ≤ μ / 2 * (‖z - xs‖ ^ 2 + ‖y - xs‖ ^ 2) := by
    rw [hxy, ← mul_assoc]
    calc
      L * (a / (1 + a)) ^ 2 * ‖z - y‖ ^ 2 ≤
          (μ / 4) * ‖z - y‖ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ ≤ (μ / 4) * (2 * (‖z - xs‖ ^ 2 + ‖y - xs‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = _ := by ring
  have hz : 0 ≤ μ / 2 * ‖z - xs‖ ^ 2 := by positivity
  nlinarith

end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/ScalarParameters.lean

namespace HighResODE.NAGSC.NSFresh

theorem scalar_parameters {μ L : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hμL : μ ≤ L) :
    let a := Real.sqrt (μ * (1 / (4 * L)))
    0 < a ∧ a ≤ 1 / 2 ∧ a ^ 2 = μ / (4 * L) ∧
      Real.sqrt (μ / L) = 2 * a := by
  dsimp
  have ht : 0 < μ * (1 / (4 * L)) := by positivity
  have ha := Real.sqrt_pos.2 ht
  have hs := Real.sq_sqrt ht.le
  have he : μ * (1 / (4 * L)) = μ / (4 * L) := by ring
  have hb : μ / (4 * L) ≤ (1 / 2 : ℝ) ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * L)).2
    nlinarith
  have hab : Real.sqrt (μ * (1 / (4 * L))) ≤ 1 / 2 := by
    have hsn := hs.trans he
    nlinarith
  refine ⟨ha, hab, hs.trans he, ?_⟩
  have hsq := Real.sq_sqrt (show 0 ≤ μ / L by positivity)
  have heq : μ / L = 4 * (μ / (4 * L)) := by field_simp
  have hn := Real.sqrt_nonneg (μ / L)
  have hsn := hs.trans he
  nlinarith

end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/RateComparison.lean

namespace HighResODE.NAGSC.NSFresh

theorem rate_power {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    (1 - a) ^ k ≤ 1 / (1 + a / 6) ^ k := by
  have hb : 0 < 1 + a / 6 := by positivity
  apply (le_div_iff₀ (pow_pos hb k)).2
  rw [← mul_pow]
  exact pow_le_one₀ (mul_nonneg (sub_nonneg.2 ha1) hb.le) (by nlinarith)

theorem energy_geometric {e : ℕ → ℝ} {a : ℝ} (ha : a ≤ 1)
    (hstep : ∀ k, e (k + 1) ≤ (1 - a) * e k) (k : ℕ) :
    e k ≤ (1 - a) ^ k * e 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      e (k + 1) ≤ (1 - a) * e k := hstep k
      _ ≤ (1 - a) * ((1 - a) ^ k * e 0) :=
        mul_le_mul_of_nonneg_left ih (sub_nonneg.2 ha)
      _ = (1 - a) ^ (k + 1) * e 0 := by ring

end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/FinalRate.lean

namespace HighResODE.NAGSC.NSFresh

theorem final_rate {μ L R : ℝ} {e F : ℕ → ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (hμL : μ ≤ L) (hR : 0 ≤ R)
    (hinit : e 0 ≤ L * R)
    (hstep : ∀ k, e (k + 1) ≤ (1 - Real.sqrt (μ * (1 / (4 * L)))) * e k)
    (hout : ∀ k, F k ≤ 3 * e k) (k : ℕ) :
    F k ≤ 5 * L * R / (1 + 1 / 12 * Real.sqrt (μ / L)) ^ k := by
  let a := Real.sqrt (μ * (1 / (4 * L)))
  obtain ⟨ha, ha2, _, hs⟩ := scalar_parameters hμ hL hμL
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have he := energy_geometric ha1 hstep k
  have hp := rate_power ha.le ha1 k
  have hLR : 0 ≤ L * R := mul_nonneg hL.le hR
  have hbase : 1 + 1 / 12 * Real.sqrt (μ / L) = 1 + a / 6 := by
    rw [hs]
    dsimp [a]
    ring
  rw [hbase]
  calc
    F k ≤ 3 * e k := hout k
    _ ≤ 3 * ((1 - a) ^ k * e 0) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ 3 * ((1 - a) ^ k * (L * R)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinit (pow_nonneg (sub_nonneg.2 ha1) k)) (by norm_num)
    _ ≤ 3 * ((1 / (1 + a / 6) ^ k) * (L * R)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hLR) (by norm_num)
    _ = 3 * (L * R) / (1 + a / 6) ^ k := by ring
    _ ≤ 5 * L * R / (1 + a / 6) ^ k := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith

end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/NativeConclusion.lean

namespace HighResODE.NAGSC.NSFresh

theorem native_theorem_3 {n : ℕ} (f : E n → ℝ) (μ L : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n)
    (hrun : IsNAGSC f μ (1 / (4 * L)) x y) :
    ∀ k : ℕ, f (x k) - f xs ≤
      5 * L * ‖x 0 - xs‖ ^ 2 / (1 + 1 / 12 * Real.sqrt (μ / L)) ^ k := by
  let a := Real.sqrt (μ * (1 / (4 * L)))
  obtain ⟨ha, ha2, hsq, _⟩ := scalar_parameters hf.mu_pos hf.isF1.L_pos hf.mu_le_L
  have hsq' : a ^ 2 = μ * (1 / (4 * L)) := by
    dsimp [a]
    simpa only [div_eq_mul_inv, one_mul] using hsq
  have hinit := run_energy_init hf xs hmin x y ha.ne' hrun.init
  have hstep := run_energy_step hf xs x y hrun ha ha2 hsq' rfl
  have hout : ∀ k, f (x k) - f xs ≤ 3 * runEnergy f μ a xs x y k := by
    intro k
    exact output_energy_bound (F := fun w => f w - f xs)
      hf.mu_pos hf.isF1.L_pos ha.le hsq (gap_lower hf xs hmin (y k))
      (gap_compare hf xs hmin (x k) (y k))
      (auxiliary_difference ha.ne' (by positivity) x y k)
  exact final_rate hf.mu_pos hf.isF1.L_pos hf.mu_le_L (sq_nonneg _)
    hinit hstep hout

end HighResODE.NAGSC.NSFresh

-- Complete module: NSProof/FinalRoot.lean
namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- Theorem 3 (Convergence of NAG-SC), p. 16: for `f ∈ S¹_{μ,L}(ℝⁿ)` and step size
`s = 1/(4L)`, the NAG-SC iterates satisfy
`f(x_k) − f(x⋆) ≤ 5L‖x₀ − x⋆‖² / (1 + (1/12)√(μ/L))^k` for all `k ≥ 0`. -/
theorem theorem_3 {n : ℕ} (f : E n → ℝ) (μ L : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n)
    (hrun : IsNAGSC f μ (1 / (4 * L)) x y) :
    ∀ k : ℕ, f (x k) - f xs ≤
      5 * L * ‖x 0 - xs‖ ^ 2 / (1 + 1 / 12 * Real.sqrt (μ / L)) ^ k := by
  exact NSFresh.native_theorem_3 f μ L hf xs hmin x y hrun

end HighResODE.NAGSC


open HighResODE.NAGSC
theorem solution {n : ℕ} (f : E n → ℝ) (μ L : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n)
    (hrun : IsNAGSC f μ (1 / (4 * L)) x y) :
    ∀ k : ℕ, f (x k) - f xs ≤
      5 * L * ‖x 0 - xs‖ ^ 2 / (1 + 1 / 12 * Real.sqrt (μ / L)) ^ k := by
  exact HighResODE.NAGSC.theorem_3 f μ L hf xs hmin x y hrun
