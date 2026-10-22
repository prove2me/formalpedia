-- Prove2me | solution 1 for JaggiFW.PrimalDual.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T15:44:23.604951+00:00
-- url     : https://prove2.me/submissions/45d4d97d-f3a1-485b-9642-41d6262439ab

/-
Primal convergence of all four Frank-Wolfe variants, Jaggi ICML2013 Theorem1.
Source mathematics: Martin Jaggi; predecessor analyses credited by the source include
Frank-Wolfe1956 and Clarkson2010. Complete linearization proof by vebis retained below
(targeteaf947dd-f270-4058-89dc-d0369b9fa8aa, submission9e0f5d73-7f5e-4d65-8c3a-390d904197f0).
New formalization proves actual curvature descent, feasibility, full-corrective hull
inclusion, comparison of all four update rules, and finite scalar convergence.
Alexander Richard Towell: research direction and stewardship. OpenAI Codex: substantial
proof construction, assembly, checking and documentation. Platform formulation: mikedeng1.
Lean/Mathlib contributors supply convex hulls, derivatives, suprema and proof infrastructure.
No mathematical novelty or independent human proof review is claimed.
-/
import Mathlib
import Definitions.Def_JaggiFW_PrimalDual_Setting

set_option autoImplicit false

open Filter Topology

lemma jfp_lin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDconv : Convex ℝ D)
    (f : E → ℝ) (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f) (x s : E) (hx : x ∈ D) (hs : s ∈ D) :
    f x + fderiv ℝ f x (s - x) ≤ f s := by
  have hdiff : DifferentiableAt ℝ f x := (hfC1.differentiable (by norm_num)) x
  set v := s - x with hv
  set g : ℝ → ℝ := fun t => f (x + t • v) with hg
  have hlin : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf0 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hdiff.hasFDerivAt
  have hgd : HasDerivAt g (fderiv ℝ f x v) 0 := hf0.comp_hasDerivAt (0 : ℝ) hlin
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hgd).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope g 0 t ≤ f s - f x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hconv := hfconv.2 hx hs (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    have e : (1 - t) • x + t • s = x + t • v := by
      rw [hv, smul_sub, sub_smul, one_smul]; abel
    rw [e] at hconv
    simp only [smul_eq_mul] at hconv
    rw [slope_def_field]
    simp only [hg, zero_smul, add_zero, sub_zero]
    rw [div_le_iff₀ ht.1]
    nlinarith
  exact (by linarith [le_of_tendsto hslope hev] : f x + fderiv ℝ f x v ≤ f s)

theorem prior_gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDc : IsCompact D) (hDconv : Convex ℝ D)
    (f : E → ℝ) (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f)
    (xstar : E) (hxstar : xstar ∈ D) (hmin : ∀ y ∈ D, f xstar ≤ f y) :
    (∀ x ∈ D, ∀ s ∈ D, f x + fderiv ℝ f x (s - x) ≤ f s) ∧
      (∀ x ∈ D, f x - f xstar ≤ JaggiFW.PrimalDual.dualityGap f D x) := by
  refine ⟨fun x hx s hs => jfp_lin D hDconv f hfC1 hfconv x s hx hs, fun x hx => ?_⟩
  have h := jfp_lin D hDconv f hfC1 hfconv x xstar hx hxstar
  unfold JaggiFW.PrimalDual.dualityGap
  have hbdd : BddAbove ((fun s => fderiv ℝ f x (x - s)) '' D) := by
    have hc : Continuous (fun s => fderiv ℝ f x (x - s)) :=
      (fderiv ℝ f x).continuous.comp (continuous_const.sub continuous_id)
    exact (hDc.image hc).bddAbove
  have this : fderiv ℝ f x (x - xstar) ≤ sSup ((fun s => fderiv ℝ f x (x - s)) '' D) :=
    le_csSup hbdd ⟨xstar, hxstar, rfl⟩
  rw [map_sub] at this
  rw [map_sub] at h
  linarith

namespace JaggiResearch
open JaggiFW.PrimalDual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma curvature_nonneg (D : Set E) (f : E → ℝ) (hCf : BddAbove (curvatureSet f D))
    (z : E) (hz : z ∈ D) : 0 ≤ curvatureConst f D := by
  apply le_csSup hCf
  refine ⟨z,hz,z,hz,1,by constructor <;> norm_num,?_⟩
  simp
lemma curvature_bound (D : Set E) (f : E → ℝ) (hCf : BddAbove (curvatureSet f D))
    (x s : E) (hx : x ∈ D) (hs : s ∈ D) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    f (x+γ • (s-x)) ≤ f x+γ*fderiv ℝ f x (s-x)+γ^2/2*curvatureConst f D := by
  have h : 2/γ^2*(f (x+γ • (s-x))-f x-fderiv ℝ f x (γ • (s-x))) ≤ curvatureConst f D :=
    le_csSup hCf ⟨x,hx,s,hs,γ,⟨hγ,hγ1⟩,rfl⟩
  rw [map_smul,smul_eq_mul] at h
  have h' : 2*(f (x+γ • (s-x))-f x-γ*fderiv ℝ f x (s-x))/γ^2 ≤ curvatureConst f D := by
    convert h using 1 <;> ring
  have hh := (div_le_iff₀ (sq_pos_of_pos hγ)).mp h'
  nlinarith only [hh]
def atoms (x s : ℕ → E) (k : ℕ) := insert (x 0) (s '' Set.Iic k)
lemma atoms_mono (x s : ℕ → E) : Monotone (atoms x s) := by
  intro k l hkl z hz
  rcases hz with hz|⟨j,hj,rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨j,le_trans hj hkl,rfl⟩
lemma feasible (D : Set E) (hD : Convex ℝ D) (f : E → ℝ) (δ Cf : ℝ) (v : Variant)
    (x s : ℕ → E) (hx0 : x 0 ∈ D) (K : ℕ)
    (hrun : ∀ k, k ≤ K → IsFWStep f D δ Cf v x s k) :
    ∀ j, j ≤ K+1 → x j ∈ D := by
  intro j hj
  induction j with
  | zero => exact hx0
  | succ j ih =>
    have hjK : j ≤ K := by omega
    have hx := ih (by omega)
    have hs := (hrun j hjK).1
    have ha : 0 ≤ 2/((j:ℝ)+2) := by positivity
    have hb : 2/((j:ℝ)+2) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; norm_num
    have hr := (hrun j hjK).2.2
    cases v with
    | alg1 => rw [hr]; exact hD hx hs (by linarith) ha (by ring)
    | alg2 => rw [hr]; exact hD hx hs (by linarith) ha (by ring)
    | alg3 =>
      obtain ⟨t,ht,he,_⟩ := hr
      rw [he]
      have heq : x j+t • (s j-x j)=(1-t) • x j+t • s j := by rw [smul_sub,sub_smul,one_smul];abel
      rw [heq]
      exact hD hx hs (by linarith [ht.2]) ht.1 (by ring)
    | alg4 =>
      apply (convexHull_min ?_ hD) hr.1
      rintro z (rfl|⟨i,hi,rfl⟩)
      · exact hx0
      · exact (hrun i (le_trans hi hjK)).1
lemma step_value (D : Set E) (f : E → ℝ) (δ Cf : ℝ) (v : Variant)
    (x s : ℕ → E) (K : ℕ) (hrun : ∀ k, k ≤ K → IsFWStep f D δ Cf v x s k)
    (k : ℕ) (hk : k ≤ K) :
    f (x (k+1)) ≤ f (x k+(2/((k:ℝ)+2)) • (s k-x k)) := by
  have ha : 0 ≤ 2/((k:ℝ)+2) := by positivity
  have hb : 2/((k:ℝ)+2) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; norm_num
  have heq : x k+(2/((k:ℝ)+2)) • (s k-x k)=
      (1-2/((k:ℝ)+2)) • x k+(2/((k:ℝ)+2)) • s k := by
    rw [smul_sub,sub_smul,one_smul];abel
  have hr := (hrun k hk).2.2
  cases v with
  | alg1 => rw [hr,heq]
  | alg2 => rw [hr,heq]
  | alg3 => exact hr.choose_spec.2.2 _ ⟨ha,hb⟩
  | alg4 =>
    have hx : x k ∈ convexHull ℝ (atoms x s k) := by
      cases k with
      | zero => exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      | succ j =>
        exact (convexHull_mono (atoms_mono x s (Nat.le_succ j))) (hrun j (by omega)).2.2.1
    have hs : s k ∈ convexHull ℝ (atoms x s k) :=
      subset_convexHull ℝ _ (Or.inr ⟨k,by simp,rfl⟩)
    apply hr.2
    rw [heq]
    exact (convex_convexHull ℝ _) hx hs (by linarith) ha (by ring)
lemma oracle (D : Set E) (f : E → ℝ) (δ Cf : ℝ) (hδ : 0 ≤ δ) (hCf : 0 ≤ Cf)
    (v : Variant) (x s : ℕ → E) (k : ℕ) (hrun : IsFWStep f D δ Cf v x s k)
    (z : E) (hz : z ∈ D) :
    fderiv ℝ f (x k) (s k) ≤ fderiv ℝ f (x k) z+1/2*δ*(2/((k:ℝ)+2))*Cf := by
  have h := hrun.2.1
  cases v with
  | alg1 => exact (h z hz).trans (le_add_of_nonneg_right (by positivity))
  | alg2 => exact h z hz
  | alg3 => exact h z hz
  | alg4 => exact h z hz
lemma primal_step (D : Set E) (hD : Convex ℝ D) (f : E → ℝ)
    (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f) (hCf : BddAbove (curvatureSet f D))
    (z : E) (hz : z ∈ D) (δ : ℝ) (hδ : 0 ≤ δ) (v : Variant) (x s : ℕ → E)
    (hx0 : x 0 ∈ D) (K : ℕ) (hrun : ∀ k, k ≤ K → IsFWStep f D δ (curvatureConst f D) v x s k)
    (k : ℕ) (hk : k ≤ K) :
    f (x (k+1))-f z ≤ (1-2/((k:ℝ)+2))*(f (x k)-f z)+
      (2/((k:ℝ)+2))^2/2*curvatureConst f D*(1+δ) := by
  have hx := feasible D hD f δ (curvatureConst f D) v x s hx0 K hrun k (by omega)
  have hs := (hrun k hk).1
  have hg : 0 < 2/((k:ℝ)+2) := by positivity
  have hg1 : 2/((k:ℝ)+2) ≤ 1 := by rw [div_le_iff₀ (by positivity)];norm_num
  have hc := curvature_bound D f hCf (x k) (s k) hx hs _ hg hg1
  have ho := oracle D f δ (curvatureConst f D) hδ (curvature_nonneg D f hCf z hz) v x s k (hrun k hk) z hz
  have hl := jfp_lin D hD f hfC1 hfconv (x k) z hx hz
  rw [map_sub] at hc hl
  have ho' := mul_le_mul_of_nonneg_left ho hg.le
  have hl' := mul_le_mul_of_nonneg_left hl hg.le
  have hv := step_value D f δ (curvatureConst f D) v x s K hrun k hk
  nlinarith only [hc,ho',hl',hv]
end JaggiResearch
#print axioms JaggiResearch.primal_step

namespace JaggiResearch
lemma scalar_primal (C : ℝ) (hC : 0 ≤ C) (h : ℕ → ℝ) (K : ℕ)
    (hs : ∀ k, k ≤ K → h (k+1) ≤ (1-2/((k:ℝ)+2))*h k+C/((k:ℝ)+2)^2) :
    ∀ j, j ≤ K+1 → 1 ≤ j → h j ≤ C/((j:ℝ)+2) := by
  intro j hj hj1
  induction j, hj1 using Nat.le_induction with
  | base =>
    have hh := hs 0 (Nat.zero_le K)
    norm_num at hh ⊢
    linarith only [hh,hC]
  | succ j hj1 ih =>
    have hjK : j ≤ K := by omega
    have hi := ih (by omega)
    have hpos : 0 < (j:ℝ)+2 := by positivity
    have hc : 0 ≤ 1-2/((j:ℝ)+2) := by
      have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
      rw [sub_nonneg,div_le_iff₀ hpos]; linarith
    calc
      h (j+1) ≤ (1-2/((j:ℝ)+2))*h j+C/((j:ℝ)+2)^2 := hs j hjK
      _ ≤ (1-2/((j:ℝ)+2))*(C/((j:ℝ)+2))+C/((j:ℝ)+2)^2 :=
        by linarith only [mul_le_mul_of_nonneg_left hi hc]
      _ = C*((j:ℝ)+1)/((j:ℝ)+2)^2 := by field_simp;ring
      _ ≤ C/((j:ℝ)+3) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hpos) (by positivity)).2
        nlinarith only [hC]
      _ = C/((↑(j+1):ℝ)+2) := by push_cast;ring
end JaggiResearch
#print axioms JaggiResearch.scalar_primal

open JaggiFW.PrimalDual

/-- Theorem 1 (primal convergence), page 4. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDc : IsCompact D) (hDconv : Convex ℝ D)
    (f : E → ℝ) (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f)
    (hCf : BddAbove (curvatureSet f D))
    (xstar : E) (hxstar : xstar ∈ D) (hmin : ∀ y ∈ D, f xstar ≤ f y)
    (δ : ℝ) (hδ : 0 ≤ δ) (v : Variant) (x s : ℕ → E) (hx0 : x 0 ∈ D)
    (hrun : ∀ k, IsFWStep f D δ (curvatureConst f D) v x s k) :
    ∀ k : ℕ, 1 ≤ k →
      f (x k) - f xstar ≤ 2 * curvatureConst f D / ((k : ℝ) + 2) * (1 + δ) := by
  intro k hk
  let C := 2*curvatureConst f D*(1+δ)
  have hC : 0 ≤ C := by
    have hc := JaggiResearch.curvature_nonneg D f hCf xstar hxstar
    dsimp [C];positivity
  have hs (j : ℕ) (hj : j ≤ k) : f (x (j+1))-f xstar ≤
      (1-2/((j:ℝ)+2))*(f (x j)-f xstar)+C/((j:ℝ)+2)^2 := by
    have hh := JaggiResearch.primal_step D hDconv f hfC1 hfconv hCf xstar hxstar δ hδ v x s hx0 k (fun i _ => hrun i) j hj
    convert hh using 1 <;> dsimp [C] <;> field_simp <;> ring
  have hh := JaggiResearch.scalar_primal C hC (fun j => f (x j)-f xstar) k hs k (by omega) hk
  dsimp [C] at hh
  convert hh using 1 <;> ring




#print axioms solution
