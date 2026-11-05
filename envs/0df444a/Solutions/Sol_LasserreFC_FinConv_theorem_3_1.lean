-- Prove2me | solution 1 for LasserreFC.FinConv.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:41:12.533758+00:00
-- url     : https://prove2.me/submissions/dc0104b9-f64e-4cb2-80ed-7bf8de92f15d

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_BHC

open MvPolynomial LasserreFC.FinConv Matrix
open scoped ContDiff

namespace LasserreFCThm31

variable {n : ℕ}

/-- `v ↦ a ⬝ᵥ v` as a continuous linear functional. -/
noncomputable def dotL (a : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ k, a k • ContinuousLinearMap.proj k

lemma dotL_apply (a v : Fin n → ℝ) : dotL a v = a ⬝ᵥ v := by
  simp [dotL, dotProduct]

lemma contDiff_eval (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℝ ℝ i)

lemma hasFDerivAt_eval (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => eval y p) (dotL (grad p x)) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine (hasFDerivAt_const a x).congr_fderiv ?_ |>.congr_of_eventuallyEq ?_
    · ext v; simp [dotL, grad]
    · exact Filter.Eventually.of_forall fun y => by simp
  | add p q hp hq =>
    refine (hp.add hq).congr_fderiv ?_ |>.congr_of_eventuallyEq ?_
    · ext v; simp [dotL_apply, grad, dotProduct, add_mul, Finset.sum_add_distrib]
    · exact Filter.Eventually.of_forall fun y => by simp
  | mul_X p i hp =>
    refine (hp.mul (hasFDerivAt_apply i x)).congr_fderiv ?_ |>.congr_of_eventuallyEq ?_
    · ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dotL_apply,
        grad, dotProduct, smul_eq_mul, ContinuousLinearMap.proj_apply, pderiv_mul, pderiv_X,
        map_add, map_mul, eval_X]
      have hs : ∀ k, eval x (Pi.single (M := fun _ : Fin n => MvPolynomial (Fin n) ℝ) k 1 i) =
          if i = k then 1 else 0 := by
        intro k; rw [Pi.single_apply]; split_ifs <;> simp
      simp only [hs, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => by ring
    · exact Filter.Eventually.of_forall fun y => by simp

lemma fderiv_eval (p : MvPolynomial (Fin n) ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => eval y p) = fun x => dotL (grad p x) :=
  funext fun x => (hasFDerivAt_eval p x).fderiv

/-- derivative of `y ↦ dotL (grad p y)` -/
lemma hasFDerivAt_dotL_grad (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => dotL (grad p y))
      (∑ k, (dotL (grad (pderiv k p) x)).smulRight (ContinuousLinearMap.proj k :
        (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have : (fun y => dotL (grad p y)) = fun y => ∑ k, (eval y (pderiv k p)) •
      (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ) := by
    funext y; simp [dotL, grad]
  rw [this]
  exact HasFDerivAt.fun_sum fun k _ => (hasFDerivAt_eval (pderiv k p) x).smul_const
    (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)

lemma second_deriv_comp {ℓ : ℕ} (p : MvPolynomial (Fin n) ℝ) (Ψ : (Fin ℓ → ℝ) → (Fin n → ℝ))
    (W : Set (Fin ℓ → ℝ)) (hW : IsOpen W) (h0 : (0 : Fin ℓ → ℝ) ∈ W)
    (hΨ : ContDiffOn ℝ ∞ Ψ W) (hg0 : grad p (Ψ 0) = 0) (w : Fin ℓ → ℝ) :
    fderiv ℝ (fderiv ℝ (fun t => eval (Ψ t) p)) 0 w w =
      (fderiv ℝ Ψ 0 w) ⬝ᵥ (hess p (Ψ 0) *ᵥ (fderiv ℝ Ψ 0 w)) := by
  have hΨat : ∀ t ∈ W, ContDiffAt ℝ ∞ Ψ t := fun t ht => hΨ.contDiffAt (hW.mem_nhds ht)
  have hev : fderiv ℝ (fun t => eval (Ψ t) p) =ᶠ[nhds 0]
      fun t => (dotL (grad p (Ψ t))).comp (fderiv ℝ Ψ t) := by
    filter_upwards [hW.mem_nhds h0] with t ht
    have hd : DifferentiableAt ℝ Ψ t := (hΨat t ht).differentiableAt (by simp)
    exact ((hasFDerivAt_eval p (Ψ t)).comp t hd.hasFDerivAt).fderiv
  rw [hev.fderiv_eq]
  have hd0 : DifferentiableAt ℝ Ψ 0 := (hΨat 0 h0).differentiableAt (by simp)
  have hc := (hasFDerivAt_dotL_grad p (Ψ 0)).comp (0 : Fin ℓ → ℝ) hd0.hasFDerivAt
  have hdd : DifferentiableAt ℝ (fderiv ℝ Ψ) 0 :=
    ((hΨat 0 h0).fderiv_right (m := 1) (by exact WithTop.coe_le_coe.2 le_top)).differentiableAt one_ne_zero
  have hcomp : HasFDerivAt (fun t => (dotL (grad p (Ψ t))).comp (fderiv ℝ Ψ t)) _ 0 :=
    hc.clm_comp hdd.hasFDerivAt
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hg0]
  have hz : dotL (0 : Fin n → ℝ) = 0 := by ext v; simp [dotL_apply]
  rw [hz]
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_apply, zero_add,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    dotL_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  set v := fderiv ℝ Ψ 0 w
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    grad, hess, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- A polynomial map `x ↦ (Q j (x))_j`. -/
noncomputable def polyMap {ι : Type*} (Q : ι → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) : ι → ℝ :=
  fun j => eval x (Q j)

noncomputable def polyMapD {ι : Type*} [Fintype ι] (Q : ι → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun j => dotL (grad (Q j) x)

lemma polyMapD_apply {ι : Type*} [Fintype ι] (Q : ι → MvPolynomial (Fin n) ℝ)
    (x v : Fin n → ℝ) (j : ι) : polyMapD Q x v j = grad (Q j) x ⬝ᵥ v := by
  simp [polyMapD, dotL_apply]

lemma hasFDerivAt_polyMap {ι : Type*} [Fintype ι] (Q : ι → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : HasFDerivAt (polyMap Q) (polyMapD Q x) x :=
  hasFDerivAt_pi.2 fun j => hasFDerivAt_eval (Q j) x

lemma contDiff_polyMap {ι : Type*} [Fintype ι] (Q : ι → MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ∞ (polyMap Q) :=
  contDiff_pi.2 fun j => contDiff_eval (Q j)

/-- The affine polynomial `x ↦ c ⬝ᵥ (x - u)`. -/
noncomputable def linPoly (c u : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ s, C (c s) * (X s - C (u s))

lemma eval_linPoly (c u x : Fin n → ℝ) : eval x (linPoly c u) = c ⬝ᵥ (x - u) := by
  simp [linPoly, dotProduct]

lemma grad_linPoly (c u x : Fin n → ℝ) : grad (linPoly c u) x = c := by
  funext k
  simp [grad, linPoly, pderiv_X, Pi.single_apply]

end LasserreFCThm31

open LasserreFCThm31 in
theorem solution {n m1 m2 : ℕ} (P : POP n m1 m2) (u : Fin n → ℝ) (hu : u ∈ P.K)
    (hloc : IsLocalMinOn (fun x => eval x P.f) P.K u) (hopt : OptCond P u) :
    IsBHC P u := by
  classical
  obtain ⟨hcqc, lam, mu, ⟨hkkt, hcomp, hmu⟩, hscc, hsosc⟩ := hopt
  obtain ⟨huh, hug⟩ := hu
  set J : Finset (Fin m2) := Finset.univ.filter (fun j => eval u (P.g j) = 0) with hJ
  set r := J.card with hr
  let ν : Fin r ↪o Fin m2 := J.orderEmbOfFin rfl
  have hνJ : ∀ j, ν j ∈ J := fun j => J.orderEmbOfFin_mem rfl j
  have hνg : ∀ j, eval u (P.g (ν j)) = 0 := fun j => by
    have := hνJ j; rw [hJ, Finset.mem_filter] at this; exact this.2
  have hJν : ∀ j, eval u (P.g j) = 0 → ∃ i, ν i = j := by
    intro j hj
    have hj' : j ∈ J := by rw [hJ, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩
    have : j ∈ Set.range ν := by
      rw [show (ν : Fin r → Fin m2) = J.orderEmbOfFin rfl from rfl, Finset.range_orderEmbOfFin]
      exact hj'
    exact this
  -- the gradient family
  let a : Fin m1 ⊕ Fin r → (Fin n → ℝ) :=
    Sum.elim (fun i => grad (P.h i) u) (fun j => grad (P.g (ν j)) u)
  have ha : LinearIndependent ℝ a := by
    have := hcqc.comp (Sum.map id (fun j => (⟨ν j, hνg j⟩ : {j : Fin m2 // eval u (P.g j) = 0})))
      (Sum.map_injective.2 ⟨Function.injective_id, fun x y hxy => by
        simpa using congrArg Subtype.val hxy⟩)
    convert this using 1
    funext x; cases x <;> rfl
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin m1 ⊕ Fin r → ℝ) := (Matrix.of a).mulVecLin
  have hA : ∀ v i, A v i = a i ⬝ᵥ v := fun v i => rfl
  set p := Module.finrank ℝ (LinearMap.ker A) with hp
  have hrank : Module.finrank ℝ (LinearMap.range A) = m1 + r := by
    have h1 : (Matrix.of a).rank = Module.finrank ℝ (LinearMap.range A) := rfl
    rw [← h1, Matrix.rank_eq_finrank_span_row, finrank_span_eq_card]
    · simp
    · exact ha
  have hdim : m1 + (r + p) = n := by
    have := LinearMap.finrank_range_add_finrank_ker A
    rw [hrank] at this
    simp at this
    omega
  let bK := Module.finBasis ℝ (LinearMap.ker A)
  have hpK : Module.finrank ℝ (LinearMap.ker A) = p := rfl
  let bK' : Module.Basis (Fin p) ℝ (LinearMap.ker A) := bK.reindex (finCongr hpK)
  let c : Fin p → (Fin n → ℝ) := fun k => (bK' k : Fin n → ℝ)
  have hcK : ∀ k, A (c k) = 0 := fun k => (bK' k).2
  let Q : Fin (r + p) → MvPolynomial (Fin n) ℝ :=
    Fin.append (fun j => P.g (ν j)) (fun k => linPoly (c k) u)
  have hQl : ∀ j, Q (Fin.castAdd p j) = P.g (ν j) := fun j => Fin.append_left _ _ j
  have hQr : ∀ k, Q (Fin.natAdd r k) = linPoly (c k) u := fun k => Fin.append_right _ _ k
  let E' := (Fin m1 → ℝ) × (Fin (r + p) → ℝ)
  let F : (Fin n → ℝ) → E' := fun x => (polyMap P.h x, polyMap Q x)
  let F' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] E' := fun x => (polyMapD P.h x).prod (polyMapD Q x)
  have hF' : ∀ x, HasFDerivAt F (F' x) x := fun x =>
    (hasFDerivAt_polyMap P.h x).prodMk (hasFDerivAt_polyMap Q x)
  have hFcd : ContDiff ℝ ∞ F := (contDiff_polyMap P.h).prodMk (contDiff_polyMap Q)
  have hF'1 : ∀ x v i, (F' x v).1 i = grad (P.h i) x ⬝ᵥ v := fun x v i => polyMapD_apply _ _ _ _
  have hF'2 : ∀ x v j, (F' x v).2 j = grad (Q j) x ⬝ᵥ v := fun x v j => polyMapD_apply _ _ _ _
  have hinj : Function.Injective (F' u) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : ∀ i, grad (P.h i) u ⬝ᵥ v = 0 := fun i => by
      rw [← hF'1, hv]; rfl
    have h2 : ∀ j, grad (Q j) u ⬝ᵥ v = 0 := fun j => by
      rw [← hF'2, hv]; rfl
    have hvK : v ∈ LinearMap.ker A := by
      rw [LinearMap.mem_ker]
      funext i
      rw [hA]
      cases i with
      | inl i => exact h1 i
      | inr j => have := h2 (Fin.castAdd p j); rw [hQl] at this; exact this
    have hcv : ∀ k, c k ⬝ᵥ v = 0 := fun k => by
      have := h2 (Fin.natAdd r k); rwa [hQr, grad_linPoly] at this
    have hrepr := bK'.sum_repr ⟨v, hvK⟩
    have hvv : v ⬝ᵥ v = 0 := by
      have : v = ∑ k, bK'.repr ⟨v, hvK⟩ k • c k := by
        have := congrArg Subtype.val hrepr
        push_cast at this
        exact this.symm
      nth_rewrite 1 [this]
      rw [sum_dotProduct]
      exact Finset.sum_eq_zero fun k _ => by rw [smul_dotProduct, hcv, smul_zero]
    exact dotProduct_self_eq_zero.1 hvv
  have hfin : Module.finrank ℝ (Fin n → ℝ) = Module.finrank ℝ E' := by
    simp [E', Module.finrank_prod, hdim]
  let e : (Fin n → ℝ) ≃L[ℝ] E' :=
    (LinearMap.linearEquivOfInjective (F' u).toLinearMap hinj hfin).toContinuousLinearEquiv
  have he : (e : (Fin n → ℝ) →L[ℝ] E') = F' u := by
    ext v <;> rfl
  have hFu' : HasFDerivAt F (e : (Fin n → ℝ) →L[ℝ] E') u := he ▸ hF' u
  let Φ := (hFcd.contDiffAt (x := u)).toOpenPartialHomeomorph F hFu' (by simp)
  have hΦ : ∀ x, Φ x = F x := fun x => rfl
  have huΦ : u ∈ Φ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
  have hFu : F u = 0 := by
    refine Prod.ext (funext fun i => huh i) (funext fun j => ?_)
    show eval u (Q j) = 0
    refine Fin.addCases (fun j => ?_) (fun k => ?_) j
    · rw [hQl]; exact hνg j
    · rw [hQr, eval_linPoly, sub_self, dotProduct_zero]
  let O : Set (Fin n → ℝ) := Φ.source ∩ {x | ∀ j, eval u (P.g j) ≠ 0 → 0 < eval x (P.g j)} ∩
    {x | fderiv ℝ F x ∈ Set.range ((↑) : ((Fin n → ℝ) ≃L[ℝ] E') → (Fin n → ℝ) →L[ℝ] E')}
  have hOsrc : O ⊆ Φ.source := fun x hx => hx.1.1
  have hOopen : IsOpen O := by
    refine (Φ.open_source.inter ?_).inter ?_
    · have : {x : Fin n → ℝ | ∀ j, eval u (P.g j) ≠ 0 → 0 < eval x (P.g j)} =
          ⋂ j, ⋂ (_ : eval u (P.g j) ≠ 0), {x | 0 < eval x (P.g j)} := by
        ext x; simp
      rw [this]
      exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
        isOpen_lt continuous_const (contDiff_eval (P.g j)).continuous
    · exact ContinuousLinearEquiv.isOpen.preimage (hFcd.continuous_fderiv (by simp))
  have huO : u ∈ O := by
    refine ⟨⟨huΦ, fun j hj => lt_of_le_of_ne (hug j) (Ne.symm hj)⟩, ⟨e, ?_⟩⟩
    rw [he, (hF' u).fderiv]
  let W : Set (Fin (r + p) → ℝ) := {t | ((0 : Fin m1 → ℝ), t) ∈ Φ '' O}
  have hWopen : IsOpen W :=
    (Φ.isOpen_image_of_subset_source hOopen hOsrc).preimage
      (continuous_const.prodMk continuous_id)
  have h0W : (0 : Fin (r + p) → ℝ) ∈ W := ⟨u, huO, by rw [hΦ, hFu]; rfl⟩
  let Ψ : (Fin (r + p) → ℝ) → (Fin n → ℝ) := fun t => Φ.symm ((0 : Fin m1 → ℝ), t)
  have hkey : ∀ t ∈ W, Ψ t ∈ O ∧ F (Ψ t) = ((0 : Fin m1 → ℝ), t) := by
    rintro t ⟨x, hxO, hxt⟩
    have : Ψ t = x := by
      show Φ.symm _ = x
      rw [← hxt]; exact Φ.left_inv (hOsrc hxO)
    rw [this]; exact ⟨hxO, hxt⟩
  have hΨ0 : Ψ 0 = u := by
    show Φ.symm _ = u
    have : ((0 : Fin m1 → ℝ), (0 : Fin (r + p) → ℝ)) = Φ u := by rw [hΦ, hFu]; rfl
    rw [this]; exact Φ.left_inv huΦ
  have hΨcd : ∀ t ∈ W, ContDiffAt ℝ ∞ Ψ t := by
    intro t ht
    obtain ⟨hO, hF⟩ := hkey t ht
    obtain ⟨ex, hex⟩ := hO.2
    have htgt : ((0 : Fin m1 → ℝ), t) ∈ Φ.target := by
      rw [← hF]; exact Φ.map_source (hOsrc hO)
    have h1 : HasFDerivAt Φ (ex : (Fin n → ℝ) →L[ℝ] E') (Φ.symm ((0 : Fin m1 → ℝ), t)) := by
      show HasFDerivAt F _ (Ψ t)
      rw [hex]; exact (hF' (Ψ t)).differentiableAt.hasFDerivAt
    have h2 := Φ.contDiffAt_symm htgt h1 hFcd.contDiffAt
    exact h2.comp t (contDiffAt_const.prodMk contDiffAt_id)
  have hΨcdOn : ContDiffOn ℝ ∞ Ψ W := fun t ht => (hΨcd t ht).contDiffWithinAt
  have hDΨ : ∀ t ∈ W, ∀ w, F' (Ψ t) (fderiv ℝ Ψ t w) = ((0 : Fin m1 → ℝ), w) := by
    intro t ht w
    have hd : DifferentiableAt ℝ Ψ t := (hΨcd t ht).differentiableAt (by simp)
    have h1 := (hF' (Ψ t)).comp t hd.hasFDerivAt
    have h2 : HasFDerivAt (fun s : Fin (r + p) → ℝ => ((0 : Fin m1 → ℝ), s))
        ((0 : (Fin (r + p) → ℝ) →L[ℝ] (Fin m1 → ℝ)).prod (ContinuousLinearMap.id ℝ _)) t :=
      (hasFDerivAt_const _ t).prodMk (hasFDerivAt_id t)
    have h3 : HasFDerivAt (F ∘ Ψ)
        ((0 : (Fin (r + p) → ℝ) →L[ℝ] (Fin m1 → ℝ)).prod (ContinuousLinearMap.id ℝ _)) t := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [hWopen.mem_nhds ht] with s hs
      exact (hkey s hs).2
    have := congrArg (fun L => L w) (h1.unique h3)
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at this
    rw [this]; rfl
  -- the Lagrangian
  set L := lagr P u lam mu with hL
  have hmuJ : ∀ j, eval u (P.g j) ≠ 0 → mu j = 0 := fun j hj => by
    rcases mul_eq_zero.1 (hcomp j) with h | h
    · exact h
    · exact absurd h hj
  have hgradL : grad L u = 0 := by
    funext k
    have hk := congrFun hkkt k
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, grad] at hk
    simp only [grad, hL, lagr, map_sub, map_sum, pderiv_C_mul, map_mul, eval_C, Pi.zero_apply]
    rw [hk, Finset.sum_filter]
    have : ∑ j, mu j * eval u (pderiv k (P.g j)) =
        ∑ j, if eval u (P.g j) = 0 then mu j * eval u (pderiv k (P.g j)) else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · rfl
      · rw [hmuJ j h, zero_mul]
    rw [this]; ring
  have hJsum : ∀ (y : Fin m2 → ℝ), ∑ j ∈ J, y j = ∑ i : Fin r, y (ν i) := by
    intro y
    conv_lhs => rw [← J.map_orderEmbOfFin_univ rfl]
    rw [Finset.sum_map]
    rfl
  have hfL : ∀ x, eval x P.f = eval x L + ∑ i, lam i * eval x (P.h i) +
      ∑ j ∈ J, mu j * eval x (P.g j) := by
    intro x; simp [hL, lagr, hJ]; ring
  let Lin : (Fin (r + p) → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin r, mu (ν i) • ContinuousLinearMap.proj (Fin.castAdd p i)
  have hLin : ∀ t, Lin t = ∑ i, mu (ν i) * t (Fin.castAdd p i) := by
    intro t; simp [Lin]
  have hcompeq : ∀ t ∈ W, eval (Ψ t) P.f = eval (Ψ t) L + Lin t := by
    intro t ht
    obtain ⟨_, hF⟩ := hkey t ht
    have h1 : ∀ i, eval (Ψ t) (P.h i) = 0 := fun i => congrFun (congrArg Prod.fst hF) i
    have h2 : ∀ j, eval (Ψ t) (Q j) = t j := fun j => congrFun (congrArg Prod.snd hF) j
    rw [hfL, hJsum, hLin]
    simp only [h1, mul_zero, Finset.sum_const_zero, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hQl, h2]
  have hDL : ∀ t ∈ W, HasFDerivAt (fun t => eval (Ψ t) L)
      ((dotL (grad L (Ψ t))).comp (fderiv ℝ Ψ t)) t := fun t ht =>
    (hasFDerivAt_eval L (Ψ t)).comp t ((hΨcd t ht).differentiableAt (by simp)).hasFDerivAt
  have hfd : ∀ t ∈ W, fderiv ℝ (fun t => eval (Ψ t) P.f) t =
      fderiv ℝ (fun t => eval (Ψ t) L) t + Lin := by
    intro t ht
    have h : HasFDerivAt (fun t => eval (Ψ t) P.f) _ t :=
      ((hDL t ht).add Lin.hasFDerivAt).congr_of_eventuallyEq (by
        filter_upwards [hWopen.mem_nhds ht] with s hs
        exact hcompeq s hs)
    rw [h.fderiv, (hDL t ht).fderiv]
  have hfd0 : fderiv ℝ (fun t => eval (Ψ t) P.f) 0 = Lin := by
    rw [hfd 0 h0W, (hDL 0 h0W).fderiv, hΨ0, hgradL]
    ext w; simp [dotL_apply]
  have hfdd0 : fderiv ℝ (fderiv ℝ (fun t => eval (Ψ t) P.f)) 0 =
      fderiv ℝ (fderiv ℝ (fun t => eval (Ψ t) L)) 0 := by
    have : fderiv ℝ (fun t => eval (Ψ t) P.f) =ᶠ[nhds 0]
        fun t => fderiv ℝ (fun t => eval (Ψ t) L) t + Lin := by
      filter_upwards [hWopen.mem_nhds h0W] with s hs
      exact hfd s hs
    rw [this.fderiv_eq, fderiv_add_const]
  have hcast : ∀ j : Fin r, Fin.castLE (Nat.le_add_right r p) j = Fin.castAdd p j :=
    fun j => rfl
  have hDΨ1 : ∀ w i, grad (P.h i) u ⬝ᵥ fderiv ℝ Ψ 0 w = 0 := by
    intro w i
    have := congrArg (fun z => z.1 i) (hDΨ 0 h0W w)
    simp only at this
    rw [hF'1, hΨ0] at this; exact this
  have hDΨ2 : ∀ w j, grad (Q j) u ⬝ᵥ fderiv ℝ Ψ 0 w = w j := by
    intro w j
    have := congrArg (fun z => z.2 j) (hDΨ 0 h0W w)
    simp only at this
    rw [hF'2, hΨ0] at this; exact this
  have himg : Ψ '' W = realVariety P ∩ O := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨hO, hF⟩ := hkey t ht
      exact ⟨fun i => congrFun (congrArg Prod.fst hF) i, hO⟩
    · rintro ⟨hV, hO⟩
      refine ⟨(F x).2, ⟨x, hO, ?_⟩, ?_⟩
      · rw [hΦ]; exact Prod.ext (funext fun i => hV i) rfl
      · show Φ.symm _ = x
        have : ((0 : Fin m1 → ℝ), (F x).2) = Φ x := by
          rw [hΦ]; exact Prod.ext (funext fun i => (hV i).symm) rfl
        rw [this]; exact Φ.left_inv (hOsrc hO)
  refine ⟨r + p, r, Nat.le_add_right r p, ν, ν.strictMono, O, W, Ψ,
    ⟨m1, P.h, hdim, fun k => ?_, ha.comp Sum.inl Sum.inl_injective⟩,
    hOopen, huO, hWopen, h0W, hΨ0, hΨcdOn, ?_, ?_, himg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_vanishingIdeal_iff]
    intro x hx; simpa using hx k
  · intro t ht x y hxy
    have h1 := hDΨ t ht x
    have h2 := hDΨ t ht y
    rw [hxy, h2] at h1
    exact (congrArg Prod.snd h1).symm
  · intro t1 ht1 t2 ht2 h
    have h1 := (hkey t1 ht1).2
    have h2 := (hkey t2 ht2).2
    rw [h, h2] at h1
    exact (congrArg Prod.snd h1).symm
  · have : ∀ x ∈ realVariety P ∩ O, Function.invFunOn Ψ W x = (F x).2 := by
      intro x hx
      have hx' : x ∈ Ψ '' W := himg ▸ hx
      have hmem := Function.invFunOn_mem hx'
      have heq := Function.invFunOn_eq hx'
      have := (hkey _ hmem).2
      rw [heq] at this
      rw [this]
    refine ContinuousOn.congr ?_ this
    exact (continuous_snd.comp hFcd.continuous).continuousOn
  · intro t ht j
    rw [hcast, ← hQl]
    exact congrFun (congrArg Prod.snd (hkey t ht).2) _
  · ext x
    constructor
    · rintro ⟨t, ⟨ht, htn⟩, rfl⟩
      obtain ⟨hO, hF⟩ := hkey t ht
      refine ⟨⟨fun i => congrFun (congrArg Prod.fst hF) i, fun j => ?_⟩, hO⟩
      by_cases hj : eval u (P.g j) = 0
      · obtain ⟨i, rfl⟩ := hJν j hj
        have := congrFun (congrArg Prod.snd hF) (Fin.castAdd p i)
        simp only [polyMap, F] at this
        rw [hQl] at this
        rw [this]; exact htn i
      · exact (hO.1.2 j hj).le
    · rintro ⟨⟨hV, hg⟩, hO⟩
      have hx : x ∈ Ψ '' W := himg ▸ ⟨hV, hO⟩
      obtain ⟨t, ht, rfl⟩ := hx
      refine ⟨t, ⟨ht, fun j => ?_⟩, rfl⟩
      have := congrFun (congrArg Prod.snd (hkey t ht).2) (Fin.castAdd p j)
      simp only [polyMap, F] at this
      rw [hQl] at this
      rw [hcast, ← this]; exact hg _
  · intro j
    rw [hfd0, hLin, hcast]
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same, mul_one]
      have := hscc (ν j); rw [hνg j, add_zero] at this; exact this
    · intro b _ hb
      rw [Pi.single_eq_of_ne (fun h => hb (Fin.castAdd_injective _ _ h)), mul_zero]
    · simp
  · intro j hj
    rw [hfd0, hLin]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    have : (Fin.castAdd p i).val = j.val := by rw [h]
    simp at this
    omega
  · intro w hw hw0
    rw [hfdd0, second_deriv_comp L Ψ W hWopen h0W hΨcdOn (by rw [hΨ0]; exact hgradL), hΨ0]
    refine hsosc _ ?_ (fun i => hDΨ1 w i) ?_
    · intro hv
      apply hw
      have := hDΨ 0 h0W w
      rw [hv, map_zero] at this
      exact (congrArg Prod.snd this).symm
    · intro j hj
      obtain ⟨i, rfl⟩ := hJν j hj
      rw [← hQl, hDΨ2]
      exact hw0 _ (by simp)
