-- Prove2me | solution 1 for IntLInfty.Kan.simplicial_pullback_forms
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:39:36.57371+00:00
-- url     : https://prove2.me/submissions/2e53e4cf-456b-450a-a109-fbae440e4378

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

-- slice of scratch/probe/a83e3b53.lean (closure of the decls used below), unit FORMS2

set_option autoImplicit false

namespace IntLInfty.Kan.A83D2

open MeasureTheory Filter Topology
open scoped ContDiff

variable {m : ℕ}

end IntLInfty.Kan.A83D2

namespace IntLInfty.Kan.A83

open IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

section FormsLin

theorem convex_simplex (m : ℕ) : Convex ℝ (simplex m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]

theorem interior_simplex_nonempty (m : ℕ) : (interior (simplex m)).Nonempty := by
  let U : Set (Fin m → ℝ) := {t | (∀ i, 0 < t i) ∧ ∑ i, t i < 1}
  have hU : IsOpen U := by
    have h1 : IsOpen {t : Fin m → ℝ | ∀ i, 0 < t i} := by
      simpa only [Set.ofPred_forall] using
        isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    have h2 : IsOpen {t : Fin m → ℝ | ∑ i, t i < 1} :=
      isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  have hsub : U ⊆ simplex m := fun t ht => ⟨fun i => (ht.1 i).le, ht.2.le⟩
  refine ⟨fun _ => 1 / ((m : ℝ) + 1), interior_mono hsub (hU.interior_eq.symm ▸ ?_)⟩
  refine ⟨fun i => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, div_lt_one (by positivity)]
  linarith

theorem uniqueDiffOn_simplex (m : ℕ) : UniqueDiffOn ℝ (simplex m) :=
  uniqueDiffOn_convex (convex_simplex m) (interior_simplex_nonempty m)

theorem contOn_iter {m k r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) (hk : k ≤ r)
    (β : Fin k → Fin m) :
    ContinuousOn (fun x => iteratedFDerivWithin ℝ k f (simplex m) x fun l => Pi.single (β l) 1)
      (simplex m) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin m → ℝ) ℝ
      (fun l => Pi.single (β l) 1)).continuous.comp_continuousOn
    (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_simplex m))

end FormsLin

section FormsLin2

variable {m r : ℕ}

end FormsLin2

open Filter Topology

section TaylorLimit

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

end TaylorLimit

section JetLimit

open IntLInfty.Kan BoundedContinuousFunction

theorem jetComp_apply {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
    (hk : k ≤ r) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f k β ⟨x, hx⟩ = iteratedFDerivWithin ℝ k f (simplex m) x (fun l => Pi.single (β l) 1) := by
  unfold jetComp
  rw [dif_pos (contOn_iter hf hk β)]
  rfl

end JetLimit

section JetClosed

open IntLInfty.Kan BoundedContinuousFunction

theorem jetComp_zero {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
    (hk : k = 0) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f k β ⟨x, hx⟩ = f x := by
  subst hk
  rw [jetComp_apply hf (Nat.zero_le _) β hx]
  rfl

theorem continuous_jet_eval {r m : ℕ} (I : Finset (Fin m)) (j : Fin (r + 1))
    (β : Fin (j : ℕ) → Fin m) : Continuous (fun w : Jet r m => w I j β) := by
  have : Continuous (fun w : ((I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) →
      (simplex m →ᵇ ℝ)) => w I j β) :=
    (continuous_apply β).comp ((continuous_apply j).comp (continuous_apply I))
  exact this

end JetClosed

section ClosedSpan

variable {m r : ℕ}

end ClosedSpan

section Rep

/-! Representative independence: the jet of a form only depends on its values on the simplex, and
it determines those values; hence `faceCr`, `faceCl`, `dCr` are computed by any representative. -/

variable {m r : ℕ}

/-- Two forms agree on the simplex. -/
def FormEqOn (ω ω' : Ω m) : Prop := ∀ x ∈ simplex m, ω x = ω' x

theorem vertex_mem (m : ℕ) (j : Fin (m + 1)) : vertex m j ∈ simplex m := by
  induction j using Fin.cases with
  | zero => exact ⟨fun _ => le_refl _, by simp [vertex]⟩
  | succ k =>
    simp only [vertex, Fin.cases_succ]
    refine ⟨fun a => ?_, ?_⟩
    · by_cases hak : a = k
      · subst hak; simp
      · simp [hak]
    · simp

end Rep

section Pull

/-! Pullback along cofaces preserves degree and the `Cʳ` condition, and commutes with `d`. -/

variable {m r : ℕ}

theorem map_mem_exteriorPower {M N : Type} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (f : M →ₗ[ℝ] N) {n : ℕ} {a : ExteriorAlgebra ℝ M} (ha : a ∈ ⋀[ℝ]^n M) :
    ExteriorAlgebra.map f a ∈ ⋀[ℝ]^n N := by
  have h1 : (⋀[ℝ]^n M).map (ExteriorAlgebra.map f).toLinearMap ≤ ⋀[ℝ]^n N := by
    show Submodule.map _ (LinearMap.range (ExteriorAlgebra.ι ℝ) ^ n) ≤
      LinearMap.range (ExteriorAlgebra.ι ℝ) ^ n
    rw [Submodule.map_pow]
    refine pow_le_pow_left' ?_ n
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, (ExteriorAlgebra.map_apply_ι f x).symm⟩
  exact h1 (Submodule.mem_map_of_mem ha)

theorem dualMap_proj {m' : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (a : Fin m') :
    L.dualMap (LinearMap.proj a) =
      ∑ k, (L (Pi.single k 1) a) • (LinearMap.proj k : (Fin m → ℝ) →ₗ[ℝ] ℝ) := by
  ext j
  simp [LinearMap.dualMap_apply, Pi.single_apply]

theorem linear_expand {m' : ℕ} {A : Type} [AddCommGroup A] [Module ℝ A]
    (T : (Fin m' → ℝ) →ₗ[ℝ] A) (v : Fin m' → ℝ) : T v = ∑ a, v a • T (Pi.single a 1) := by
  conv_lhs => rw [← (Pi.basisFun ℝ (Fin m')).sum_repr v]
  simp only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr]

theorem wedge_natural {m' : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ))
    (T : (Fin m' → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m' → ℝ))) :
    ExteriorAlgebra.map L.dualMap (∑ a, dx m' a * T (Pi.single a 1)) =
      ∑ k, dx m k * ExteriorAlgebra.map L.dualMap (T (L (Pi.single k 1))) := by
  simp only [map_sum, map_mul, dx, ExteriorAlgebra.map_apply_ι, dualMap_proj, map_smul,
    Finset.sum_mul, smul_mul_assoc]
  conv_rhs => enter [2, k]; rw [linear_expand T (L (Pi.single k 1))]
  simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_comm

end Pull

section PullAff

/-! Pullback along an arbitrary affine map `x ↦ b + L x` sending `Δᵐ` into `Δᵐ'` (the retractions
used by the horn-extension operator of Lemma 5.9 are of this kind). -/

variable {m m' r : ℕ}

/-- Pullback of forms along the affine map `x ↦ b + L x`. -/
noncomputable def pullA (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω : Ω m') : Ω m :=
  fun x => ExteriorAlgebra.map L.dualMap (ω (b + L x))

theorem pullA_isDeg {n : ℕ} {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'} (h : IsDeg n ω) :
    IsDeg n (pullA b L ω) := fun x hx =>
  map_mem_exteriorPower _ (h _ (hA x hx))

/-- The coefficients of the pulled-back basis forms. -/
noncomputable def pcA (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (I : Finset (Fin m'))
    (J : Finset (Fin m)) : ℝ :=
  (formBasis m).repr (ExteriorAlgebra.map L.dualMap (formBasis m' I)) J

theorem coeff_pullA (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω : Ω m')
    (J : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (pullA b L ω) J x = ∑ I, coeff ω I (b + L x) * pcA L I J := by
  simp only [coeff, pullA, pcA]
  conv_lhs => rw [← (formBasis m').sum_repr (ω (b + L x))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem hasFDerivAt_aff (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (x : Fin m → ℝ) :
    HasFDerivAt (fun x => b + L x) (LinearMap.toContinuousLinearMap L) x :=
  (LinearMap.toContinuousLinearMap L).hasFDerivAt.const_add _

theorem contDiff_aff {n : WithTop ℕ∞} (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) :
    ContDiff ℝ n (fun x => b + L x) :=
  contDiff_const.add (LinearMap.toContinuousLinearMap L).contDiff

theorem contDiffOn_coeff_pullA {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'}
    (h : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) (J : Finset (Fin m)) :
    ContDiffOn ℝ r (coeff (pullA b L ω) J) (simplex m) := by
  rw [show coeff (pullA b L ω) J = fun x => ∑ I, coeff ω I (b + L x) * pcA L I J from
    funext (coeff_pullA b L ω J)]
  exact ContDiffOn.sum fun I _ =>
    ((h I).comp (contDiff_aff b L).contDiffOn (fun x hx => hA x hx)).mul contDiffOn_const

theorem extD_pullA (hr : 1 ≤ r) {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'}
    (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (pullA b L ω) x = pullA b L (extD ω) x := by
  have hy : b + L x ∈ simplex m' := hA x hx
  have hd : ∀ I, HasFDerivWithinAt (coeff ω I)
      (fderivWithin ℝ (coeff ω I) (simplex m') (b + L x)) (simplex m') (b + L x) := fun I =>
    (((hC I).differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) _ hy).hasFDerivWithinAt
  have hpd : ∀ J (k : Fin m), fderivWithin ℝ (coeff (pullA b L ω) J) (simplex m) x (Pi.single k 1) =
      ∑ I, fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) (L (Pi.single k 1)) * pcA L I J := by
    intro J k
    have e : coeff (pullA b L ω) J = fun x => ∑ I, coeff ω I (b + L x) * pcA L I J :=
      funext (coeff_pullA b L ω J)
    have hH : HasFDerivWithinAt (fun x => ∑ I, coeff ω I (b + L x) * pcA L I J)
        (∑ I, (pcA L I J) • ((fderivWithin ℝ (coeff ω I) (simplex m') (b + L x)).comp
          (LinearMap.toContinuousLinearMap L))) (simplex m) x := by
      refine HasFDerivWithinAt.fun_sum (u := Finset.univ) fun I _ => ?_
      exact ((hd I).comp x (hasFDerivAt_aff b L x).hasFDerivWithinAt
        (fun z hz => hA z hz)).mul_const (pcA L I J)
    rw [e, hH.fderivWithin (uniqueDiffOn_simplex m x hx)]
    simp [mul_comm]
  let T : (Fin m' → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m' → ℝ)) :=
    ∑ I, ((fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) :
      (Fin m' → ℝ) →L[ℝ] ℝ) : (Fin m' → ℝ) →ₗ[ℝ] ℝ).smulRight (formBasis m' I)
  have hT : ∀ v, T v = ∑ I, fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) v •
      formBasis m' I := by
    intro v; simp [T]
  have hR : pullA b L (extD ω) x = ExteriorAlgebra.map L.dualMap
      (∑ a, dx m' a * T (Pi.single a 1)) := by
    simp only [hT]; rfl
  rw [hR, wedge_natural]
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [hT]
  simp only [hpd, map_sum, map_smul, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact (formBasis m).sum_repr _

theorem pullA_isCr (hr : 1 ≤ r) {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'} (hC : IsCr r ω) :
    IsCr r (pullA b L ω) := fun J =>
  ⟨contDiffOn_coeff_pullA hA (fun I => (hC I).1) J,
    (contDiffOn_coeff_pullA hA (fun I => (hC I).2) J).congr fun x hx => by
      show (formBasis m).repr (extD (pullA b L ω) x) J = (formBasis m).repr (pullA b L (extD ω) x) J
      rw [extD_pullA hr hA (fun I => (hC I).1) hx]⟩

theorem pullA_isClosedForm (hr : 1 ≤ r) {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'} (hC : IsCr r ω)
    (h : IsClosedForm ω) : IsClosedForm (pullA b L ω) := fun x hx => by
  rw [extD_pullA hr hA (fun I => (hC I).1) hx]
  show ExteriorAlgebra.map _ (extD ω (b + L x)) = 0
  rw [h _ (hA x hx), map_zero]

/-- Pullback is linear (pointwise, everywhere). -/
theorem pullA_add (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω ω' : Ω m') :
    pullA b L (ω + ω') = pullA b L ω + pullA b L ω' := by
  funext x; simp [pullA, map_add]

theorem pullA_smul (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (c : ℝ) (ω : Ω m') :
    pullA b L (c • ω) = c • pullA b L ω := by
  funext x; simp [pullA, map_smul]

/-- Functoriality: pulling back along `A ∘ B` is pulling back along `A`, then along `B`. -/
theorem pullA_comp {m'' : ℕ} (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ))
    (b' : Fin m → ℝ) (L' : (Fin m'' → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (ω : Ω m') :
    pullA b' L' (pullA b L ω) = pullA (b + L b') (L ∘ₗ L') ω := by
  funext x
  simp only [pullA, LinearMap.comp_apply, map_add, add_assoc]
  rw [← LinearMap.dualMap_comp_dualMap, ← ExteriorAlgebra.map_comp_map]
  rfl

/-- Pullback respects agreement on the simplex. -/
theorem pullA_congr {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω ω' : Ω m'} (h : FormEqOn ω ω') :
    FormEqOn (pullA b L ω) (pullA b L ω') := fun x hx => by
  simp only [pullA, h _ (hA x hx)]

end PullAff

section PullS

/-! Simplicial pullbacks: the affine map `Δᵐ → Δᵐ'` sending the vertex `v_l` to `v_{θ l}` for any
`θ : Fin (m+1) → Fin (m'+1)` (cofaces, codegeneracies and the horn retractions), and functoriality. -/

variable {m m' r : ℕ}

/-- The linear part of the affine map with vertex images `w`. -/
noncomputable def affL (w : Fin (m + 1) → (Fin m' → ℝ)) : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ) :=
  (Matrix.of fun (a : Fin m') (k : Fin m) => (w k.succ - w 0) a).mulVecLin

theorem affL_apply (w : Fin (m + 1) → (Fin m' → ℝ)) (x : Fin m → ℝ) :
    affL w x = ∑ k, x k • (w k.succ - w 0) := by
  funext a
  simp [affL, Matrix.mulVec, dotProduct, mul_comm]

theorem aff_vertex (w : Fin (m + 1) → (Fin m' → ℝ)) (l : Fin (m + 1)) :
    w 0 + affL w (vertex m l) = w l := by
  induction l using Fin.cases with
  | zero => simp [vertex]
  | succ k =>
    rw [affL_apply]
    simp [vertex, Pi.single_apply]

theorem aff_mem {w : Fin (m + 1) → (Fin m' → ℝ)} (hw : ∀ l, w l ∈ simplex m') :
    ∀ x ∈ simplex m, w 0 + affL w x ∈ simplex m' := by
  intro x hx
  let c : Fin (m + 1) → ℝ := Fin.cons (1 - ∑ k, x k) x
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ c j := by
    intro j _
    induction j using Fin.cases with
    | zero => simp only [c, Fin.cons_zero]; linarith [hx.2]
    | succ k => simp only [c, Fin.cons_succ]; exact hx.1 k
  have h1 : ∑ j, c j = 1 := by
    rw [Fin.sum_univ_succ]; simp only [c, Fin.cons_zero, Fin.cons_succ]; ring
  have hm := (convex_simplex m').sum_mem h0 h1 (z := w) (fun j _ => hw j)
  convert hm using 1
  rw [affL_apply, Fin.sum_univ_succ]
  simp only [c, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul,
    one_smul, ← Finset.sum_smul]
  abel

/-- An affine map is determined by its vertex images. -/
theorem aff_ext {w : Fin (m + 1) → (Fin m' → ℝ)} {b : Fin m' → ℝ}
    {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)} (h : ∀ l, b + L (vertex m l) = w l) :
    b = w 0 ∧ L = affL w := by
  have hb : b = w 0 := by
    have := h 0
    simpa [vertex] using this
  refine ⟨hb, LinearMap.ext fun x => ?_⟩
  rw [linear_expand L x, linear_expand (affL w) x]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have h1 := h a.succ
  have h2 := aff_vertex w a.succ
  simp only [vertex, Fin.cases_succ] at h1 h2
  rw [hb] at h1
  exact add_left_cancel (h1.trans h2.symm)

/-- Pullback along the simplicial affine map with vertex map `θ`. -/
noncomputable def pullS (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m') : Ω m :=
  pullA (vertex m' (θ 0)) (affL fun l => vertex m' (θ l)) ω

theorem pullS_mem (θ : Fin (m + 1) → Fin (m' + 1)) :
    ∀ x ∈ simplex m, vertex m' (θ 0) + (affL fun l => vertex m' (θ l)) x ∈ simplex m' :=
  aff_mem (w := fun l => vertex m' (θ l)) fun l => vertex_mem _ _

theorem pullS_comp {m'' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (θ' : Fin (m'' + 1) → Fin (m + 1))
    (ω : Ω m') : pullS θ' (pullS θ ω) = pullS (θ ∘ θ') ω := by
  simp only [pullS]
  rw [pullA_comp]
  obtain ⟨h1, h2⟩ := aff_ext (w := fun l => vertex m' (θ (θ' l)))
    (b := vertex m' (θ 0) + (affL fun l => vertex m' (θ l)) (vertex m (θ' 0)))
    (L := (affL fun l => vertex m' (θ l)) ∘ₗ (affL fun l => vertex m (θ' l))) (fun l => by
      rw [LinearMap.comp_apply, add_assoc, ← map_add,
        aff_vertex (fun l => vertex m (θ' l)) l, aff_vertex (fun l => vertex m' (θ l)) (θ' l)])
  rw [h1, h2]
  rfl

theorem pullS_isDeg {n : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'} (h : IsDeg n ω) :
    IsDeg n (pullS θ ω) := pullA_isDeg (pullS_mem θ) h

theorem pullS_isCr (hr : 1 ≤ r) (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'} (hC : IsCr r ω) :
    IsCr r (pullS θ ω) := pullA_isCr hr (pullS_mem θ) hC

theorem pullS_isClosedForm (hr : 1 ≤ r) (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'}
    (hC : IsCr r ω) (h : IsClosedForm ω) : IsClosedForm (pullS θ ω) :=
  pullA_isClosedForm hr (pullS_mem θ) hC h

theorem extD_pullS (hr : 1 ≤ r) (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'}
    (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    extD (pullS θ ω) x = pullS θ (extD ω) x := extD_pullA hr (pullS_mem θ) hC hx

theorem pullS_congr (θ : Fin (m + 1) → Fin (m' + 1)) {ω ω' : Ω m'} (h : FormEqOn ω ω') :
    FormEqOn (pullS θ ω) (pullS θ ω') := pullA_congr (pullS_mem θ) h

theorem pullS_id (ω : Ω m) : FormEqOn (pullS id ω) ω := fun x _ => by
  obtain ⟨h1, h2⟩ := aff_ext (w := fun l => vertex m (id l)) (b := 0)
    (L := LinearMap.id) (fun l => by simp)
  simp only [pullS, pullA]
  rw [← h1, ← h2]
  simp [LinearMap.dualMap_id, ExteriorAlgebra.map_id]

end PullS

section HornExt

/-! Horn filling for forms at the level of representatives (Lemma 5.9, surjectivity): the classical
inductive extension, correcting face by face with pullbacks along the retraction `retr i j` of
`Δᵐ⁺¹` onto its `i`-th face that moves the vertex `i` to the vertex `j`. -/

variable {m r : ℕ}

theorem pullS_add' {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m') :
    pullS θ (ω + ω') = pullS θ ω + pullS θ ω' := pullA_add _ _ _ _

theorem pullS_sub {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m') :
    pullS θ (ω - ω') = pullS θ ω - pullS θ ω' := by
  funext x; simp [pullS, pullA, map_sub]

end HornExt

section HornJet

/-! Lemma 5.9 surjectivity at the jet level: a compatible tuple of jets (codim-2 identities only)
lifts to a strongly compatible tuple of representatives, which then fills. -/

variable {m r : ℕ}

end HornJet

section Fold

/-! The horn-filling operator as an explicit fold (linear in the tuple, respects `FormEqOn`):
the input to the closed-graph argument for a continuous linear section. -/

variable {m r : ℕ}

theorem pullS_smul' {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (c : ℝ) (ω : Ω m') :
    pullS θ (c • ω) = c • pullS θ ω := pullA_smul _ _ _ _

end Fold

section ClosedGraph

/-! Continuity of the face maps and of the horn section by the closed graph theorem: limits in the
jet space control the coefficients pointwise (order-0 jet components), and pullbacks / folds
preserve pointwise convergence of coefficients. -/

variable {m r : ℕ}

/-- Pointwise convergence of all coefficients on the simplex. -/
def CoeffTendsto (ωk : ℕ → Ω m) (ω : Ω m) : Prop :=
  ∀ I, ∀ x ∈ simplex m, Tendsto (fun k => coeff (ωk k) I x) atTop (𝓝 (coeff ω I x))

theorem coeffTendsto_pullS {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) {ωk : ℕ → Ω m'}
    {ω : Ω m'} (h : CoeffTendsto ωk ω) :
    CoeffTendsto (fun k => pullS θ (ωk k)) (pullS θ ω) := by
  intro J x hx
  simp only [pullS, coeff_pullA]
  exact tendsto_finset_sum _ fun I _ => (h I _ (pullS_mem θ x hx)).mul_const _

theorem coeffTendsto_of_jet {ωk : ℕ → Ω m} {ω : Ω m} (hk : ∀ k, IsCr r (ωk k)) (hω : IsCr r ω)
    (h : Tendsto (fun k => jet r (ωk k)) atTop (𝓝 (jet r ω))) : CoeffTendsto ωk ω := by
  intro I x hx
  let j0 : Fin (r + 1) := 0
  have hj0 : (j0 : ℕ) = 0 := rfl
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have hc : Continuous (fun w : Jet r m × Jet r m => w.1 I j0 β0 ⟨x, hx⟩) :=
    (continuous_eval_const _).comp
      ((continuous_jet_eval I j0 β0).comp continuous_fst)
  have t := (hc.tendsto _).comp h
  have e1 : (jet r ω).1 I j0 β0 ⟨x, hx⟩ = coeff ω I x := jetComp_zero (hω I).1 hj0 β0 hx
  rw [Function.comp_def, e1] at t
  exact t.congr fun k => jetComp_zero ((hk k) I).1 hj0 β0 hx

end ClosedGraph

section HornSection

/-! The continuous linear horn section `E` (fold of retraction pullbacks on representatives),
the simplicial identities for `faceCr`, and Lemma 5.9 for `Ωⁿ_{Cʳ}`. -/

variable {m r : ℕ}

end HornSection

section Lemma59

/-! Lemma 5.9 for `Ωⁿ_{Cʳ}(Δ^•)`: horn sets are closed complemented subspaces (the range of the
continuous projection `hornMap ∘ E`), and `hornMap` is a surjective submersion with the affine
  right inverse `y ↦ x + E (y - hornMap x)`. -/

variable {m r : ℕ}

end Lemma59

section Lemma59Closed

/-! Lemma 5.9 for closed forms `Ωⁿ_closed(Δ^•)`: same argument with closed representatives. -/

variable {m r : ℕ}

end Lemma59Closed

end IntLInfty.Kan.A83

open IntLInfty.Kan in
theorem solution (r : ℕ) (hr : 1 ≤ r)
    (P : (m m' : ℕ) → (Fin (m + 1) → Fin (m' + 1)) → Ω m' → Ω m)
    (hP : ∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m') (x : Fin m → ℝ),
      P m m' θ ω x = ExteriorAlgebra.map
        (Matrix.of fun (a : Fin m') (k : Fin m) =>
          (vertex m' (θ k.succ) - vertex m' (θ 0)) a).mulVecLin.dualMap
        (ω (vertex m' (θ 0) + (Matrix.of fun (a : Fin m') (k : Fin m) =>
          (vertex m' (θ k.succ) - vertex m' (θ 0)) a).mulVecLin x))) :
    (∀ (m : ℕ) (i : Fin (m + 2)) (ω : Ω (m + 1)), pull m i ω = P m (m + 1) i.succAbove ω) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)), ∀ x ∈ simplex m,
      vertex m' (θ 0) + (Matrix.of fun (a : Fin m') (k : Fin m) =>
        (vertex m' (θ k.succ) - vertex m' (θ 0)) a).mulVecLin x ∈ simplex m') ∧
    (∀ (m m' m'' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (θ' : Fin (m'' + 1) → Fin (m + 1))
      (ω : Ω m'), P m'' m θ' (P m m' θ ω) = P m'' m' (θ ∘ θ') ω) ∧
    (∀ (m : ℕ) (ω : Ω m), ∀ x ∈ simplex m, P m m id ω x = ω x) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m'),
      P m m' θ (ω + ω') = P m m' θ ω + P m m' θ ω') ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m'),
      P m m' θ (ω - ω') = P m m' θ ω - P m m' θ ω') ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (c : ℝ) (ω : Ω m'),
      P m m' θ (c • ω) = c • P m m' θ ω) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (n : ℕ) (ω : Ω m'),
      IsDeg n ω → IsDeg n (P m m' θ ω)) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m'), IsCr r ω → IsCr r (P m m' θ ω)) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m'),
      IsCr r ω → IsClosedForm ω → IsClosedForm (P m m' θ ω)) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m'),
      (∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) →
        ∀ x ∈ simplex m, extD (P m m' θ ω) x = P m m' θ (extD ω) x) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m'),
      (∀ x ∈ simplex m', ω x = ω' x) → ∀ x ∈ simplex m, P m m' θ ω x = P m m' θ ω' x) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ωk : ℕ → Ω m') (ω : Ω m'),
      (∀ I, ∀ x ∈ simplex m',
        Filter.Tendsto (fun k => coeff (ωk k) I x) Filter.atTop (nhds (coeff ω I x))) →
      ∀ J, ∀ x ∈ simplex m, Filter.Tendsto (fun k => coeff (P m m' θ (ωk k)) J x) Filter.atTop
        (nhds (coeff (P m m' θ ω) J x))) ∧
    (∀ (r' m : ℕ) (ωk : ℕ → Ω m) (ω : Ω m), (∀ k, IsCr r' (ωk k)) → IsCr r' ω →
      Filter.Tendsto (fun k => jet r' (ωk k)) Filter.atTop (nhds (jet r' ω)) →
      ∀ I, ∀ x ∈ simplex m,
        Filter.Tendsto (fun k => coeff (ωk k) I x) Filter.atTop (nhds (coeff ω I x))) := by
  obtain rfl : P = fun _ _ θ ω => A83.pullS θ ω := by
    funext m m' θ ω x
    exact hP m m' θ ω x
  exact ⟨fun _ _ _ => rfl, fun _ _ θ => A83.pullS_mem θ,
    fun _ _ _ θ θ' ω => A83.pullS_comp θ θ' ω, fun _ ω x hx => A83.pullS_id ω x hx,
    fun _ _ θ ω ω' => A83.pullS_add' θ ω ω', fun _ _ θ ω ω' => A83.pullS_sub θ ω ω',
    fun _ _ θ c ω => A83.pullS_smul' θ c ω, fun _ _ θ _ _ h => A83.pullS_isDeg θ h,
    fun _ _ θ _ h => A83.pullS_isCr hr θ h, fun _ _ θ _ hC h => A83.pullS_isClosedForm hr θ hC h,
    fun _ _ θ _ hC _ hx => A83.extD_pullS hr θ hC hx, fun _ _ θ _ _ h => A83.pullS_congr θ h,
    fun _ _ θ _ _ h => A83.coeffTendsto_pullS θ h,
    fun _ _ _ _ hk hω h => A83.coeffTendsto_of_jet hk hω h⟩
