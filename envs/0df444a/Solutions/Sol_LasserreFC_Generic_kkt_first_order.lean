-- Prove2me | solution 1 for LasserreFC.Generic.kkt_first_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:05:33.997254+00:00
-- url     : https://prove2.me/submissions/12c9e167-f52c-44c5-a17e-cba9d37b32ea

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting

namespace LasserreFC.Generic.KKTRed

open MvPolynomial LasserreFC.Generic

variable {n : ℕ}

noncomputable def gradL (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) :
    StrongDual ℝ (Fin n → ℝ) :=
  ∑ k, (eval u (pderiv k p)) • ContinuousLinearMap.proj k

lemma gradL_apply (p : MvPolynomial (Fin n) ℝ) (u z : Fin n → ℝ) :
    gradL p u z = grad p u ⬝ᵥ z := by
  simp [gradL, grad, dotProduct]

lemma hasStrictFDerivAt_eval (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) :
    HasStrictFDerivAt (fun x => eval x p) (gradL p u) u := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : gradL (C a) u = 0 := by ext z; simp [gradL]
    rw [this]
    have e : (fun x : Fin n → ℝ => eval x (C a)) = fun _ => a := by funext x; simp
    rw [e]
    exact hasStrictFDerivAt_const a u
  | add p q hp hq =>
    have : gradL (p + q) u = gradL p u + gradL q u := by
      ext z; simp [gradL, add_mul, Finset.sum_add_distrib]
    rw [this]
    have e : (fun x : Fin n → ℝ => eval x (p + q)) = fun x => eval x p + eval x q := by
      funext x; simp
    rw [e]
    exact hp.add hq
  | mul_X p i hp =>
    have hX : HasStrictFDerivAt (fun x : Fin n → ℝ => x i)
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) u :=
      hasStrictFDerivAt_apply i u
    have h := hp.mul hX
    have hd : ∀ k, pderiv k (p * X i) = pderiv k p * X i + (if k = i then p else 0) := by
      intro k
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, add_comm, mul_comm (X i)]
      congr 1
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk, Ne.symm hk]
    have : gradL (p * X i) u = eval u p • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) +
        u i • gradL p u := by
      ext z
      rw [gradL_apply]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, gradL_apply, grad, dotProduct, hd, map_add,
        map_mul, eval_X, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · simp [apply_ite (eval u)]
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
    rw [this]
    have e : (fun x : Fin n → ℝ => eval x (p * X i)) = fun x => eval x p * x i := by
      funext x; simp
    rw [e]
    exact h

end LasserreFC.Generic.KKTRed

namespace LasserreFC.Generic.KKTRed

open MvPolynomial LasserreFC.Generic Filter Topology Matrix

variable {n : ℕ}

/-- linearly independent rows ⇒ `M *ᵥ ·` is onto -/
lemma surj_of_li {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι (Fin n) ℝ)
    (hM : LinearIndependent ℝ M.row) (y : ι → ℝ) : ∃ z, M *ᵥ z = y := by
  have hr := hM.rank_matrix
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, ← hr]
    rfl
  have : y ∈ LinearMap.range M.mulVecLin := by rw [htop]; trivial
  obtain ⟨z, hz⟩ := this
  exact ⟨z, hz⟩

/-- the vector of values of finitely many polynomials -/
lemma hasStrictFDerivAt_vec {ι : Type*} [Fintype ι] (q : ι → MvPolynomial (Fin n) ℝ)
    (u : Fin n → ℝ) :
    HasStrictFDerivAt (fun x => fun e => eval x (q e))
      (ContinuousLinearMap.pi fun e => gradL (q e) u) u :=
  hasStrictFDerivAt_pi.2 fun e => by simpa using hasStrictFDerivAt_eval (q e) u

lemma range_pi_eq_top {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → MvPolynomial (Fin n) ℝ)
    (u : Fin n → ℝ) (hli : LinearIndependent ℝ (fun e => grad (q e) u)) :
    (ContinuousLinearMap.pi fun e => gradL (q e) u).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  obtain ⟨z, hz⟩ := surj_of_li (Matrix.of fun e k => grad (q e) u k) hli y
  refine ⟨z, ?_⟩
  rw [← hz]
  funext e
  simp [gradL_apply, Matrix.mulVec]

variable {m1 m2 : ℕ}

/-- the active constraint polynomials `h₁, …, h_{m₁}, g_j (j ∈ J(u))` -/
def actPoly (P : POP n m1 m2) (u : Fin n → ℝ) :
    Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} → MvPolynomial (Fin n) ℝ :=
  Sum.elim P.h (fun j => P.g j.1)

lemma cqc_iff (P : POP n m1 m2) (u : Fin n → ℝ) :
    CQC P u ↔ LinearIndependent ℝ (fun e => grad (actPoly P u e) u) := by
  have : (fun e => grad (actPoly P u e) u) = Sum.elim (fun i : Fin m1 => grad (P.h i) u)
      (fun j : {j : Fin m2 // eval u (P.g j) = 0} => grad (P.g j.1) u) := by
    funext e; rcases e with i | j <;> rfl
  rw [this]; rfl

lemma actPoly_zero {P : POP n m1 m2} {u : Fin n → ℝ} (hu : u ∈ P.K) (e) :
    eval u (actPoly P u e) = 0 := by
  rcases e with i | ⟨j, hj⟩
  · exact hu.1 i
  · exact hj

lemma inactive_nhds {P : POP n m1 m2} {u : Fin n → ℝ} (hu : u ∈ P.K) :
    ∀ᶠ x in 𝓝 u, ∀ j, eval u (P.g j) ≠ 0 → 0 < eval x (P.g j) := by
  rw [Filter.eventually_all]
  intro j
  by_cases hj : eval u (P.g j) = 0
  · exact Filter.Eventually.of_forall (fun _ h => absurd hj h)
  · have hpos : 0 < eval u (P.g j) := lt_of_le_of_ne (hu.2 j) (Ne.symm hj)
    have hc : ContinuousAt (fun x => eval x (P.g j)) u :=
      (hasStrictFDerivAt_eval _ u).hasFDerivAt.continuousAt
    exact (hc.eventually (lt_mem_nhds hpos)).mono (fun x hx _ => hx)

lemma exists_nu {P : POP n m1 m2} {u : Fin n → ℝ} (hu : u ∈ P.K)
    (hmin : IsLocalMinOn (fun x => eval x P.f) P.K u) (hcq : CQC P u) :
    ∃ ν : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} → ℝ,
      grad P.f u = ∑ e, ν e • grad (actPoly P u e) u := by
  classical
  let E := {x : Fin n → ℝ | ∀ e, eval x (actPoly P u e) = eval u (actPoly P u e)}
  have hloc : IsLocalMinOn (fun x => eval x P.f) E u := by
    have hV := inactive_nhds hu
    have hsub : E ∩ {x | ∀ j, eval u (P.g j) ≠ 0 → 0 < eval x (P.g j)} ⊆ P.K := by
      rintro x ⟨hxE, hxV⟩
      refine ⟨fun i => ?_, fun j => ?_⟩
      · have := hxE (Sum.inl i)
        rw [actPoly_zero hu] at this
        exact this
      · by_cases hj : eval u (P.g j) = 0
        · have := hxE (Sum.inr ⟨j, hj⟩)
          rw [actPoly_zero hu] at this
          exact le_of_eq this.symm
        · exact (hxV j hj).le
    have h1 := hmin.on_subset hsub
    exact IsMinFilter.filter_mono h1
      (le_of_eq (nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hV)).symm)
  obtain ⟨Λ, Λ0, hne, hsum⟩ := IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt (Or.inl hloc)
    (f := fun e x => eval x (actPoly P u e)) (fun e => hasStrictFDerivAt_eval _ u)
    (hasStrictFDerivAt_eval P.f u)
  have hcomp : ∀ k, ∑ e, Λ e * grad (actPoly P u e) u k + Λ0 * grad P.f u k = 0 := by
    intro k
    have := congrArg (fun L => L (Pi.single k 1)) hsum
    simpa [gradL_apply] using this
  have hΛ0 : Λ0 ≠ 0 := by
    intro h0
    apply hne
    have hΛ : Λ = 0 := by
      have hli := (cqc_iff P u).mp hcq
      funext e
      refine Fintype.linearIndependent_iff.mp hli Λ ?_ e
      funext k
      have := hcomp k
      rw [h0, zero_mul, add_zero] at this
      simpa [Finset.sum_apply] using this
    rw [hΛ, h0]
    rfl
  refine ⟨fun e => -Λ e / Λ0, ?_⟩
  funext k
  have := hcomp k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hΛ0
  rw [Finset.mul_sum]
  have h2 : ∀ e, Λ0 * (-Λ e / Λ0 * grad (actPoly P u e) u k) =
      -(Λ e * grad (actPoly P u e) u k) := fun e => by field_simp
  simp_rw [h2]
  rw [Finset.sum_neg_distrib]
  linarith

lemma nu_nonneg {P : POP n m1 m2} {u : Fin n → ℝ} (hu : u ∈ P.K)
    (hmin : IsLocalMinOn (fun x => eval x P.f) P.K u) (hcq : CQC P u)
    (ν : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} → ℝ)
    (hν : grad P.f u = ∑ e, ν e • grad (actPoly P u e) u)
    (j0 : {j : Fin m2 // eval u (P.g j) = 0}) : 0 ≤ ν (Sum.inr j0) := by
  classical
  have hli := (cqc_iff P u).mp hcq
  obtain ⟨D, hD⟩ := surj_of_li (Matrix.of fun e k => grad (actPoly P u e) u k) hli
    (Pi.single (Sum.inr j0) 1)
  have hDe : ∀ e, grad (actPoly P u e) u ⬝ᵥ D =
      (Pi.single (Sum.inr j0) (1 : ℝ) : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} → ℝ) e := by
    intro e; rw [← hD]; rfl
  let q' : {e : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0} // e ≠ Sum.inr j0} →
      MvPolynomial (Fin n) ℝ := fun e => actPoly P u e.1
  have hli' : LinearIndependent ℝ (fun e => grad (q' e) u) :=
    hli.comp Subtype.val Subtype.val_injective
  let F := fun x : Fin n → ℝ => fun e => eval x (q' e)
  let F' := ContinuousLinearMap.pi fun e => gradL (q' e) u
  have hF : HasStrictFDerivAt F F' u := hasStrictFDerivAt_vec q' u
  have hsurj : F'.range = ⊤ := range_pi_eq_top q' u hli'
  have hDker : D ∈ F'.ker := by
    rw [LinearMap.mem_ker]
    funext e
    simp only [F', ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply, gradL_apply,
      Pi.zero_apply, q']
    rw [hDe, Pi.single_apply, if_neg e.2]
  let Dk : F'.ker := ⟨D, hDker⟩
  let x : ℝ → (Fin n → ℝ) := fun t => hF.implicitFunction F F' hsurj (F u) (t • Dk)
  have hx0 : x 0 = u := by
    simp only [x, zero_smul]
    exact hF.implicitFunction_apply_image hsurj
  have hxd : HasDerivAt x D 0 := by
    have h1 := (hF.to_implicitFunction hsurj).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => t • Dk) Dk 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const Dk
    have := h1.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
    exact this
  have hxF : ∀ᶠ t in 𝓝 (0 : ℝ), F (x t) = F u := by
    have h := hF.map_implicitFunction_eq hsurj
    have ht : Tendsto (fun t : ℝ => (F u, t • Dk)) (𝓝 0) (𝓝 (F u, 0)) := by
      apply tendsto_const_nhds.prodMk_nhds
      have : Tendsto (fun t : ℝ => t • Dk) (𝓝 0) (𝓝 ((0 : ℝ) • Dk)) :=
        (continuous_id.smul continuous_const).tendsto 0
      simpa using this
    exact ht.eventually h
  have hxc : Tendsto x (𝓝 0) (𝓝 u) := by
    have := hxd.continuousAt
    rw [ContinuousAt, hx0] at this
    exact this
  have hcomp : ∀ p : MvPolynomial (Fin n) ℝ,
      HasDerivAt (fun t => eval (x t) p) (grad p u ⬝ᵥ D) 0 := by
    intro p
    have h := (hasStrictFDerivAt_eval p u).hasFDerivAt
    have := h.comp_hasDerivAt_of_eq (0 : ℝ) hxd hx0.symm
    rw [gradL_apply] at this
    exact this
  have hg : HasDerivAt (fun t => eval (x t) (P.g j0.1)) 1 0 := by
    have := hcomp (P.g j0.1)
    have e1 : grad (P.g j0.1) u ⬝ᵥ D = 1 := by
      have := hDe (Sum.inr j0)
      simpa [actPoly] using this
    rwa [e1] at this
  have hf : HasDerivAt (fun t => eval (x t) P.f) (ν (Sum.inr j0)) 0 := by
    have := hcomp P.f
    have e1 : grad P.f u ⬝ᵥ D = ν (Sum.inr j0) := by
      rw [hν, sum_dotProduct]
      simp only [smul_dotProduct, hDe, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rwa [e1] at this
  have hgpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < eval (x t) (P.g j0.1) := by
    have hsl := hg.tendsto_slope_zero_right
    have hev := hsl.eventually (lt_mem_nhds (zero_lt_one' ℝ))
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
    simp only [zero_add, hx0, smul_eq_mul, j0.2, sub_zero] at ht
    have htpos' : (0 : ℝ) < t := htpos
    have := mul_pos htpos' ht
    rwa [← mul_assoc, mul_inv_cancel₀ htpos'.ne', one_mul] at this
  have hK : ∀ᶠ t in 𝓝[>] (0 : ℝ), x t ∈ P.K := by
    have hV : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, eval u (P.g j) ≠ 0 → 0 < eval (x t) (P.g j) :=
      (hxc.mono_left nhdsWithin_le_nhds).eventually (inactive_nhds hu)
    have hF' : ∀ᶠ t in 𝓝[>] (0 : ℝ), F (x t) = F u := nhdsWithin_le_nhds hxF
    filter_upwards [hV, hF', hgpos] with t h1 h2 h3
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := congrFun h2 ⟨Sum.inl i, by simp⟩
      simp only [F, q', actPoly, Sum.elim_inl] at this
      rw [this]
      exact hu.1 i
    · by_cases hj : eval u (P.g j) = 0
      · by_cases hj0 : j = j0.1
        · subst hj0; exact h3.le
        · have hne : (Sum.inr ⟨j, hj⟩ : Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) ≠
              Sum.inr j0 := by
            intro h
            apply hj0
            have := Sum.inr_injective h
            rw [← this]
          have := congrFun h2 ⟨Sum.inr ⟨j, hj⟩, hne⟩
          simp only [F, q', actPoly, Sum.elim_inr] at this
          rw [this, hj]
      · exact (h1 j hj).le
  have hfge : ∀ᶠ t in 𝓝[>] (0 : ℝ), eval u P.f ≤ eval (x t) P.f := by
    have htK : Tendsto x (𝓝[>] 0) (𝓝[P.K] u) :=
      tendsto_nhdsWithin_iff.mpr ⟨hxc.mono_left nhdsWithin_le_nhds, hK⟩
    exact htK.eventually hmin
  have hsl := hf.tendsto_slope_zero_right
  apply ge_of_tendsto hsl
  filter_upwards [hfge, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_add, hx0, smul_eq_mul]
  have htpos' : (0 : ℝ) < t := htpos
  exact mul_nonneg (inv_nonneg.mpr htpos'.le) (sub_nonneg.mpr ht)

end LasserreFC.Generic.KKTRed

open MvPolynomial LasserreFC.Generic LasserreFC.Generic.KKTRed in
theorem solution {n m1 m2 : ℕ} (P : POP n m1 m2) (u : Fin n → ℝ) (hu : u ∈ P.K)
    (hmin : IsLocalMinOn (fun x => eval x P.f) P.K u) (hcq : CQC P u) :
    ∃ (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ), IsKKTMult P u lam mu := by
  classical
  obtain ⟨ν, hν⟩ := exists_nu hu hmin hcq
  refine ⟨fun i => ν (Sum.inl i),
    fun j => if h : eval u (P.g j) = 0 then ν (Sum.inr ⟨j, h⟩) else 0, ?_, ?_, ?_⟩
  · rw [hν, Fintype.sum_sum_type]
    congr 1
    have h1 : ∑ j, (if h : eval u (P.g j) = 0 then ν (Sum.inr ⟨j, h⟩) else 0) • grad (P.g j) u =
        ∑ j ∈ Finset.univ.filter (fun j => eval u (P.g j) = 0),
          (if h : eval u (P.g j) = 0 then ν (Sum.inr ⟨j, h⟩) else 0) • grad (P.g j) u := by
      symm
      apply Finset.sum_filter_of_ne
      intro j _ hj
      by_contra h
      apply hj
      rw [dif_neg h, zero_smul]
    rw [h1, Finset.sum_subtype (Finset.univ.filter (fun j => eval u (P.g j) = 0))
      (p := fun j => eval u (P.g j) = 0) (fun j => by simp)
      (fun j => (if h : eval u (P.g j) = 0 then ν (Sum.inr ⟨j, h⟩) else 0) • grad (P.g j) u)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [dif_pos j.2]
    rfl
  · intro j
    by_cases h : eval u (P.g j) = 0
    · dsimp only; rw [dif_pos h, h, mul_zero]
    · dsimp only; rw [dif_neg h, zero_mul]
  · intro j
    by_cases h : eval u (P.g j) = 0
    · dsimp only; rw [dif_pos h]
      exact nu_nonneg hu hmin hcq ν hν ⟨j, h⟩
    · dsimp only; rw [dif_neg h]
