-- Prove2me | solution 1 for MathematicalRelativity.penrose_singularity_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T18:44:35.274973+00:00
-- url     : https://prove2.me/submissions/db331418-564f-4f16-a2e3-087f0871d4df

import Mathlib
import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

set_option autoImplicit false

open scoped ContDiff
open Filter Topology

namespace MathematicalRelativity

/-- Minkowski space in the global chart. -/
noncomputable def mink : Spacetime where
  g := fun _ i j => eta i j
  smooth := fun _ _ => contDiff_const
  symm := by
    intro x i j
    simp only [eta, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  lorentz := by
    intro x
    refine ⟨1, by simp, ?_⟩
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  time_orient := by
    intro x
    simp [eta]

lemma mink_ip (x u v : Pt) :
    mink.ip x u v = -(u 0 * v 0) + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 := by
  simp [Spacetime.ip, mink, eta, Matrix.diagonal_apply, Fin.sum_univ_four]

lemma mink_christoffel (a b c : Fin 4) : mink.christoffel a b c = fun _ => 0 := by
  funext x
  simp [Spacetime.christoffel, pd, mink]

lemma mink_ricciQuad (x v : Pt) : mink.ricciQuad x v = 0 := by
  simp [Spacetime.ricciQuad, Spacetime.ricci, Spacetime.riemann, mink_christoffel, pd]

lemma mink_complete : mink.GeodesicallyComplete := by
  intro x v
  refine ⟨fun t => fun a => x a + t * v a, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a
    exact (contDiff_const.add (contDiff_id.mul contDiff_const)).contDiffOn
  · intro t _ a
    have h1 : (fun s => deriv (fun u => x a + u * v a) s) = fun _ => v a := by
      funext s
      have : HasDerivAt (fun u => x a + u * v a) (v a) s := by
        simpa using ((hasDerivAt_id s).mul_const (v a)).const_add (x a)
      exact this.deriv
    simp [acc, mink_christoffel, h1]
  · funext a; simp
  · funext a
    simp only [vel]
    have : HasDerivAt (fun u => x a + u * v a) (v a) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v a)).const_add (x a)
    exact this.deriv

/-- The slice `x⁰ = 0`. -/
noncomputable def minkSlice : Slice mink where
  f := fun x => x 0
  f_smooth := contDiff_apply ℝ ℝ 0
  N := fun _ => fun i => if i = 0 then 1 else 0
  N_smooth := fun _ => contDiff_const
  N_unit := by intro x; rw [mink_ip]; simp
  N_future := by intro x; simp [Spacetime.IsFuture]
  N_normal := by
    intro x
    refine ⟨-1, by norm_num, ?_⟩
    intro a
    have hd : fderiv ℝ (fun y : Pt => y 0) x = ContinuousLinearMap.proj 0 :=
      (hasFDerivAt_apply 0 x).fderiv
    simp only [pd, hd, ContinuousLinearMap.proj_apply]
    fin_cases a <;> simp [Spacetime.lower, mink, eta, Matrix.diagonal_apply, Fin.sum_univ_four]

/-- The empty surface. -/
noncomputable def emptySurf : Surface mink minkSlice where
  U := ∅
  U_open := isOpen_empty
  h := fun _ => 1
  h_smooth := contDiffOn_const
  n := fun _ => 0
  n_smooth := fun _ => contDiffOn_const
  n_unit := by simp
  n_orth := by simp
  n_normal := by simp
  subset := by intro x hx; simp at hx
  compact := by
    have : {x : Pt | minkSlice.f x = 0 ∧ (fun _ : Pt => (1:ℝ)) x = 0} = ∅ := by
      ext x; simp
    rw [this]; exact isCompact_empty

lemma emptySurf_trapped : emptySurf.IsTrapped := by
  intro x hx
  simp [Surface.carrier, emptySurf] at hx

lemma mink_nec : mink.NullEnergyCondition := by
  intro x v _
  rw [mink_ricciQuad]

lemma slice_noncompact : ¬ IsCompact minkSlice.carrier := by
  intro hc
  have himg := hc.image (continuous_apply (1 : Fin 4))
  have : (fun x : Pt => x 1) '' minkSlice.carrier = Set.univ := by
    ext r
    simp only [Set.mem_image, Set.mem_univ, iff_true]
    refine ⟨fun i => if i = 1 then r else 0, ?_, by simp⟩
    simp [Slice.carrier, minkSlice]
  rw [this] at himg
  exact noncompact_univ ℝ himg

/-- bounded-above lemma for a pair of monotone functions with bounded sum -/
lemma bdd_of_pair (f k : ℝ → ℝ) (hf : Monotone f) (hk : Monotone k) (M : ℝ)
    (hM : ∀ t, 0 ≤ t → f t + k t ≤ M) : BddAbove (Set.range f) := by
  refine ⟨max (f 0) (M - k 0), ?_⟩
  rintro _ ⟨t, rfl⟩
  rcases le_total t 0 with ht | ht
  · exact le_max_of_le_left (hf ht)
  · have := hM t ht
    have := hk ht
    exact le_max_of_le_right (by linarith)

lemma bddB_of_pair (f k : ℝ → ℝ) (hf : Monotone f) (hk : Monotone k) (M : ℝ)
    (hM : ∀ t, t ≤ 0 → M ≤ f t + k t) : BddBelow (Set.range f) := by
  refine ⟨min (f 0) (M - k 0), ?_⟩
  rintro _ ⟨t, rfl⟩
  rcases le_total t 0 with ht | ht
  · have := hM t ht
    have := hk ht
    exact min_le_of_right_le (by linarith)
  · exact min_le_of_left_le (hf ht)

section causal

variable (c : ℝ → Pt) (hc : mink.IsCausalCurveOn c Set.univ)
include hc

lemma cdiff (a : Fin 4) : Differentiable ℝ (fun s => c s a) := by
  have := (hc.1 a)
  rw [contDiffOn_univ] at this
  exact this.differentiable (by norm_num)

lemma vel_bound (t : ℝ) (i : Fin 4) : |vel c t i| ≤ vel c t 0 := by
  obtain ⟨⟨hle, _⟩, hfut⟩ := hc.2 t (Set.mem_univ t)
  rw [mink_ip] at hle
  simp only [Spacetime.IsFuture] at hfut
  have hsq : vel c t i ^ 2 ≤ vel c t 0 ^ 2 := by
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (vel c t 1), sq_nonneg (vel c t 2),
      sq_nonneg (vel c t 3)]
  have := sq_le_sq.1 hsq
  rwa [abs_of_pos hfut] at this

lemma mono_plus (i : Fin 4) : Monotone (fun t => c t 0 + c t i) := by
  apply monotone_of_deriv_nonneg ((cdiff c hc 0).add (cdiff c hc i))
  intro t
  rw [deriv_add ((cdiff c hc 0) t) ((cdiff c hc i) t)]
  have := vel_bound c hc t i
  have h2 := neg_abs_le (vel c t i)
  simp only [vel] at this h2
  linarith

lemma mono_minus (i : Fin 4) : Monotone (fun t => c t 0 - c t i) := by
  apply monotone_of_deriv_nonneg ((cdiff c hc 0).sub (cdiff c hc i))
  intro t
  rw [deriv_sub ((cdiff c hc 0) t) ((cdiff c hc i) t)]
  have := vel_bound c hc t i
  have h2 := le_abs_self (vel c t i)
  simp only [vel] at this h2
  linarith

lemma strict0 : StrictMono (fun t => c t 0) := by
  apply strictMono_of_deriv_pos
  intro t
  have := (hc.2 t (Set.mem_univ t)).2
  simpa [Spacetime.IsFuture, vel] using this

lemma tendsto_of_eq (f k : ℝ → ℝ) (l : Filter ℝ) (a b : ℝ) (i : Fin 4)
    (hf : Tendsto f l (𝓝 a)) (hk : Tendsto k l (𝓝 b))
    (hfe : f = fun t => c t 0 + c t i) (hke : k = fun t => c t 0 - c t i) :
    Tendsto (fun t => c t i) l (𝓝 ((a - b) / 2)) := by
  have := (hf.sub hk).div_const 2
  refine this.congr (fun t => ?_)
  subst hfe hke
  simp only
  ring

lemma conv_top (L : ℝ) (hL : ∀ t, c t 0 ≤ L) : ∃ p : Pt, Tendsto c atTop (𝓝 p) := by
  have key : ∀ i, ∃ q, Tendsto (fun t => c t i) atTop (𝓝 q) := by
    intro i
    have hb1 := bdd_of_pair _ _ (mono_plus c hc i) (mono_minus c hc i) (2 * L)
      (fun t _ => by have := hL t; linarith)
    have hb2 := bdd_of_pair _ _ (mono_minus c hc i) (mono_plus c hc i) (2 * L)
      (fun t _ => by have := hL t; linarith)
    exact ⟨_, tendsto_of_eq c hc _ _ atTop _ _ i (tendsto_atTop_ciSup (mono_plus c hc i) hb1)
      (tendsto_atTop_ciSup (mono_minus c hc i) hb2) rfl rfl⟩
  choose q hq using key
  exact ⟨q, tendsto_pi_nhds.2 hq⟩

lemma conv_bot (L : ℝ) (hL : ∀ t, L ≤ c t 0) : ∃ p : Pt, Tendsto c atBot (𝓝 p) := by
  have key : ∀ i, ∃ q, Tendsto (fun t => c t i) atBot (𝓝 q) := by
    intro i
    have hb1 := bddB_of_pair _ _ (mono_plus c hc i) (mono_minus c hc i) (2 * L)
      (fun t _ => by have := hL t; linarith)
    have hb2 := bddB_of_pair _ _ (mono_minus c hc i) (mono_plus c hc i) (2 * L)
      (fun t _ => by have := hL t; linarith)
    exact ⟨_, tendsto_of_eq c hc _ _ atBot _ _ i (tendsto_atBot_ciInf (mono_plus c hc i) hb1)
      (tendsto_atBot_ciInf (mono_minus c hc i) hb2) rfl rfl⟩
  choose q hq using key
  exact ⟨q, tendsto_pi_nhds.2 hq⟩

end causal

lemma slice_cauchy : mink.IsCauchySurface minkSlice.carrier := by
  intro c ⟨hc, htop, hbot⟩
  have hmem : ∀ t, c t ∈ minkSlice.carrier ↔ c t 0 = 0 := fun t => Iff.rfl
  have hcont : Continuous (fun t => c t 0) := (cdiff c hc 0).continuous
  have hpos : ∃ t, 0 ≤ c t 0 := by
    by_contra h
    push_neg at h
    exact htop (conv_top c hc 0 (fun t => (h t).le))
  have hneg : ∃ t, c t 0 ≤ 0 := by
    by_contra h
    push_neg at h
    exact hbot (conv_bot c hc 0 (fun t => (h t).le))
  obtain ⟨t1, ht1⟩ := hpos
  obtain ⟨t2, ht2⟩ := hneg
  have hsm := strict0 c hc
  have hle : t2 ≤ t1 := by
    by_contra h
    push_neg at h
    have := hsm h
    simp only at this
    linarith
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hle hcont.continuousOn ⟨ht2, ht1⟩
  refine ⟨t, (hmem t).2 ht, fun s hs => ?_⟩
  exact hsm.injective (((hmem s).1 hs).trans ht.symm)

end MathematicalRelativity

open MathematicalRelativity in
theorem solution : ¬ (∀ (m : Spacetime) (S : Slice m) (Sig : Surface m S)
    (hcauchy : m.IsCauchySurface S.carrier)
    (hnoncompact : ¬ IsCompact S.carrier)
    (hnec : m.NullEnergyCondition)
    (htrapped : Sig.IsTrapped),
    m.IsSingular) := by
  intro H
  exact H mink minkSlice emptySurf slice_cauchy slice_noncompact mink_nec emptySurf_trapped
    mink_complete
