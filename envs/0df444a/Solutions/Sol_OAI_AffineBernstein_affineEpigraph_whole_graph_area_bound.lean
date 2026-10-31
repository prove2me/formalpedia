-- Prove2me | solution 1 for OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:59:01.949628+00:00
-- url     : https://prove2.me/submissions/fc8e9551-633d-431f-9b21-e4951e6f7c7f

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_product_area_chart

section
-- module Solutions.OAIQ22_AB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DeterminantVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

theorem hessian_eq_second {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    hessian u x i j =
      fderiv ℝ (fderiv ℝ u) x (coordinateVector n i) (coordinateVector n j) := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (coordinateVector n j) x)
  unfold hessian
  rw [he.fderiv]
  simp

theorem second_fderiv_eq_sum {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (v : Space n) :
    fderiv ℝ (fderiv ℝ u) x v v =
    ∑ i, ∑ j, v i * hessian u x i j * v j := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x (∑ i, v i • coordinateVector n i)
        (∑ j, v j • coordinateVector n j) := by rw [sum_coordinateVector]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hessian_eq_second hu,
        hu.isSymmSndFDerivAt (by simp)
          (coordinateVector n j) (coordinateVector n i)]
      ring

theorem second_fderiv_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosSemidef) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_nonneg (fun i => v i)

theorem second_fderiv_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  have hv' : (fun i => v i) ≠ 0 := fun he => hv (by ext i; exact congrFun he i)
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_pos hv'

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphPatchArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem convexOn_of_hessian_posSemidef {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    ConvexOn ℝ Ω u := by
  refine ⟨hcv, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (u ∘ γ) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hf hdf hdd
      (fun t ht => second_fderiv_nonneg
        (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
        (hp _ (hseg t (interior_subset ht))) (y - x))
  have he := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have heq : γ b = a • x + b • y := by
    dsimp [γ]
    rw [smul_sub]
    have ha' : a = 1 - b := by linarith
    rw [ha', sub_smul, one_smul]
    abel
  simpa [Function.comp_def, γ, heq, smul_eq_mul] using he

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

section CompleteSphericalDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SupportGeometry
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The literal support value, not a freely chosen support coordinate. -/
theorem convex_first_order {W : Set E} {F : E → ℝ} (hF : ConvexOn ℝ W F)
    {x y : E} (hx : x ∈ W) (hy : y ∈ W) (hd : DifferentiableAt ℝ F x) :
    fderiv ℝ F x (y - x) ≤ F y - F x := by
  let γ : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t => x + t • (y - x)
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (y - x)
      map_vadd' := by intro t s; simp [add_smul]; abel }
  have hc := hF.comp_affineMap γ
  have hdγ : HasDerivAt γ (y - x) 0 := by
    change HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hdx : HasFDerivAt F (fderiv ℝ F x) (γ 0) := by
    simpa [γ] using hd.hasFDerivAt
  have hs := hc.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simpa [γ] using hx) (by simpa [γ] using hy) (by norm_num)
    (by simpa [γ] using hdx.comp_hasDerivAt 0 hdγ)
  simpa [slope_def_field, γ] using hs

/- A nonzero linear functional cannot attain its sublevel maximum below the level. -/
theorem sublevel_max_on_level {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {z : E} (hz : z ∈ W)
    (hzF : F z ≤ 0) (hc : ContinuousAt F z)
    (hmax : IsMaxOn ℓ {y | y ∈ W ∧ F y ≤ 0} z) : F z = 0 := by
  by_contra hn
  have ht : F z < 0 := lt_of_le_of_ne hzF hn
  have hm : IsLocalMax ℓ z := by
    filter_upwards [hW.mem_nhds hz, hc.eventually (eventually_lt_nhds ht)] with y hy hyF
    exact hmax ⟨hy, hyF.le⟩
  exact hℓ (by simpa using hm.fderiv_eq_zero)

/- The support maximum of a compact smooth convex sublevel has a positive
Lagrange multiplier. This includes dimension one without a sphere convention. -/
theorem exists_support_multiplier [CompleteSpace E] {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) (hF : ContDiffOn ℝ ∞ F W)
    {x₀ : E} (hx₀ : x₀ ∈ W) (hneg : F x₀ < 0)
    (hK : IsCompact {y | y ∈ W ∧ F y ≤ 0})
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ∃ z ∈ W, F z = 0 ∧ ∃ lam : ℝ, 0 < lam ∧
      fderiv ℝ F z = lam • ℓ ∧
      (∀ y ∈ W, F y ≤ 0 → ℓ y ≤ ℓ z) ∧
      supportValue {y | y ∈ W ∧ F y ≤ 0} ℓ = ℓ z := by
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀, hneg.le⟩ ℓ.continuous.continuousOn
  have hd := hF.contDiffAt (hW.mem_nhds hz.1)
  have hzF := sublevel_max_on_level hW hℓ hz.1 hz.2 hd.continuousAt hmax
  have he : IsLocalExtrOn ℓ {y | F y = F z} z := by
    apply Or.inr
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hz.1)]
      with y hy hyW
    exact hmax ⟨hyW, by simp [hy, hzF]⟩
  obtain ⟨a, b, hab, heq⟩ := he.exists_multipliers_of_hasStrictFDerivAt_1d
    (hd.hasStrictFDerivAt (by simp)) ℓ.hasStrictFDerivAt
  have ha : a ≠ 0 := by
    intro ha
    have hb : b ≠ 0 := by simpa [ha] using hab
    simp only [ha, zero_smul, zero_add] at heq
    exact hℓ ((smul_eq_zero.mp heq).resolve_left hb)
  let lam := -b / a
  have hder : fderiv ℝ F z = lam • ℓ := by
    ext v
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) heq
    simp only [add_apply, smul_apply, zero_apply, smul_eq_mul] at hh ⊢
    dsimp [lam]
    field_simp
    nlinarith
  have hi := convex_first_order hcv hz.1 hx₀ (hd.differentiableAt (by simp))
  rw [hder, smul_apply, smul_eq_mul, hzF, sub_zero] at hi
  have hlin : ℓ (x₀ - z) ≤ 0 := by
    rw [map_sub, sub_nonpos]
    exact hmax ⟨hx₀, hneg.le⟩
  have hlam : 0 < lam := by
    by_contra ht
    have hh := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ht) hlin
    linarith
  refine ⟨z, hz.1, hzF, lam, hlam, hder, ?_, ?_⟩
  · intro y hy hyF
    exact hmax ⟨hy, hyF⟩
  · unfold supportValue
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (s := ℓ '' {y | y ∈ W ∧ F y ≤ 0}) ?_ ?_ ?_
    · exact ⟨ℓ z, z, hz, rfl⟩
    · rintro v ⟨y, hy, rfl⟩; exact hmax hy
    · intro b hb
      exact ⟨ℓ z, ⟨z, hz, rfl⟩, hb⟩

/- Linearization of the actual support equations `F(y)=0`, `DF(y)=lam*ell`. -/
theorem supportJacobian_injective {d : E →L[ℝ] ℝ}
    {H : E →L[ℝ] (E →L[ℝ] ℝ)} {ℓ : E →L[ℝ] ℝ} {lam : ℝ}
    (hℓ : ℓ ≠ 0) (hlam : lam ≠ 0) (hd : d = lam • ℓ)
    (hH : ∀ v : E, v ≠ 0 → 0 < H v v) :
    Function.Injective (supportJacobian d H ℓ) := by
  apply (injective_iff_map_eq_zero (supportJacobian d H ℓ)).mpr
  rintro ⟨v, a⟩ hv
  change (d v, H v - a • ℓ) = (0, 0) at hv
  have hv1 : d v = 0 := congrArg Prod.fst hv
  have hv2 : H v = a • ℓ := sub_eq_zero.mp (congrArg Prod.snd hv)
  have hlv : ℓ v = 0 := by
    simpa [hd, hlam] using hv1
  have hv0 : v = 0 := by
    by_contra hn
    have hh := hH v hn
    rw [hv2] at hh
    simp [hlv] at hh
  have ha0 : a = 0 := by
    rw [hv0, map_zero] at hv2
    exact (smul_eq_zero.mp hv2.symm).resolve_right hℓ
  simp [hv0, ha0]

theorem supportJacobian_isInvertible [FiniteDimensional ℝ E]
    {d : E →L[ℝ] ℝ} {H : E →L[ℝ] (E →L[ℝ] ℝ)}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hℓ : ℓ ≠ 0) (hlam : lam ≠ 0)
    (hd : d = lam • ℓ) (hH : ∀ v : E, v ≠ 0 → 0 < H v v) :
    (supportJacobian d H ℓ).IsInvertible := by
  have hi := supportJacobian_injective hℓ hlam hd hH
  have hf : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ (ℝ × (E →L[ℝ] ℝ)) := by
    rw [Module.finrank_prod, Module.finrank_prod,
      ← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq,
      Subspace.dual_finrank_eq]
    omega
  let e := (supportJacobian d H ℓ).toLinearMap.linearEquivOfInjective hi hf
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- Fiber derivatives of the actual defining function. -/

theorem contDiffAt_fiberGradient {F : S × E → ℝ} {p : S × E}
    (hF : ContDiffAt ℝ ∞ F p) : ContDiffAt ℝ ∞ (fiberGradient F) p := by
  apply ContDiffAt.fderiv (n := ∞) (g := Prod.snd) _ contDiffAt_snd (by simp)
  exact hF.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)

theorem contDiffAt_supportEquations {F : S × E → ℝ} {s : S} {y : E}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hF : ContDiffAt ℝ ∞ F (s, y)) :
    ContDiffAt ℝ ∞ (supportEquations F) ((s, ℓ), (y, lam)) := by
  have he : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd.fst
  have hc1 : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      F (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) := hF.comp ((s, ℓ), (y, lam)) he
  have hc2 : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      fiberGradient F (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) := by
    have hh := (contDiffAt_fiberGradient (F := F) (p := (s, y)) hF).comp ((s, ℓ), (y, lam)) he
    exact hh
  exact hc1.prodMk (hc2.sub (contDiffAt_snd.snd.smul contDiffAt_fst.snd))

theorem supportEquations_partial {F : S × E → ℝ} {s : S} {y : E}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hF : ContDiffAt ℝ ∞ F (s, y)) :
    fderiv ℝ (supportEquations F) ((s, ℓ), (y, lam)) ∘L
      ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ) =
    supportJacobian (fderiv ℝ (fun z => F (s, z)) y)
      (fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y) ℓ := by
  have hfu : ContDiffAt ℝ ∞ (fun z => F (s, z)) y :=
    hF.comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hdu := hfu.differentiableAt (by simp)
  have h2u := (hfu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hp : HasFDerivAt (fun q : E × ℝ => supportEquations F ((s, ℓ), q))
      (supportJacobian (fderiv ℝ (fun z => F (s, z)) y)
        (fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y) ℓ) (y, lam) := by
    exact (hdu.hasFDerivAt.comp (y, lam) (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).prodMk
      ((h2u.hasFDerivAt.comp (y, lam) (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).sub
        ((ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.smul_const ℓ))
  have hi : HasFDerivAt (fun q : E × ℝ => ((s, ℓ), q))
      (ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ)) (y, lam) := by
    convert (hasFDerivAt_const (s, ℓ) (y, lam)).prodMk (hasFDerivAt_id (y, lam)) using 1 <;>
      ext <;> simp
  exact (((contDiffAt_supportEquations (ℓ := ℓ) (lam := lam) hF).differentiableAt
    (by simp)).hasFDerivAt.comp (y, lam) hi).unique hp

/- A solution of the support equations with positive multiplier is a global,
not merely local, support point. -/
theorem supportValue_of_equations {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {z : E} (hz : z ∈ W) (hzF : F z = 0)
    (hd : DifferentiableAt ℝ F z) {ℓ : E →L[ℝ] ℝ} {lam : ℝ}
    (hlam : 0 < lam) (he : fderiv ℝ F z = lam • ℓ) :
    supportValue {y | y ∈ W ∧ F y ≤ 0} ℓ = ℓ z := by
  unfold supportValue
  have hmax (y : E) (hy : y ∈ W ∧ F y ≤ 0) : ℓ y ≤ ℓ z := by
    have hh := convex_first_order hcv hz hy.1 hd
    simp only [he, smul_apply, smul_eq_mul, map_sub, hzF, sub_zero] at hh
    have hh' : lam * (ℓ y - ℓ z) ≤ 0 := by simpa [mul_sub] using hh.trans hy.2
    nlinarith
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (s := ℓ '' {y | y ∈ W ∧ F y ≤ 0}) ?_ ?_ ?_
  · exact ⟨ℓ z, z, ⟨hz, hzF.le⟩, rfl⟩
  · rintro v ⟨y, hy, rfl⟩; exact hmax y hy
  · intro a ha; exact ⟨ℓ z, ⟨z, ⟨hz, hzF.le⟩, rfl⟩, ha⟩

/- Smooth dependence of the literal support value on base and conormal.
The IFT is applied to the actual defining function and its actual Hessian. -/
theorem contDiffAt_supportValue_fibers [FiniteDimensional ℝ E] [CompleteSpace S]
    {B : Set S} (hB : IsOpen B) {W : Set (S × E)} (hW : IsOpen W)
    {F : S × E → ℝ} (hF : ContDiffOn ℝ ∞ F W)
    (hcv : ∀ s ∈ B, ConvexOn ℝ {y | (s, y) ∈ W} (fun y => F (s, y)))
    {s : S} (hs : s ∈ B) {x₀ : E} (hx₀ : (s, x₀) ∈ W) (hneg : F (s, x₀) < 0)
    (hK : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0})
    (hH : ∀ y, (s, y) ∈ W → F (s, y) = 0 → ∀ v : E, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y v v)
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ W ∧ F (q.1, y) ≤ 0} q.2) (s, ℓ) := by
  have hWs : IsOpen {y | (s, y) ∈ W} := hW.preimage (by fun_prop)
  have hFs : ContDiffOn ℝ ∞ (fun y => F (s, y)) {y | (s, y) ∈ W} :=
    hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  obtain ⟨z, hz, hzF, lam, hlam, hder, -, hsup⟩ :=
    exists_support_multiplier hWs (hcv s hs) hFs hx₀ hneg hK hℓ
  have hcF := hF.contDiffAt (hW.mem_nhds hz)
  have hg := contDiffAt_supportEquations (ℓ := ℓ) (lam := lam) hcF
  have hinv : (fderiv ℝ (supportEquations F) ((s, ℓ), (z, lam)) ∘L
      ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ)).IsInvertible := by
    rw [supportEquations_partial hcF]
    exact supportJacobian_isInvertible hℓ hlam.ne' hder (hH z hz hzF)
  let ψ := hg.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ∞ ψ (s, ℓ) := hg.contDiffAt_implicitFunction (by simp) hinv
  have hψ₀ : ψ (s, ℓ) = (z, lam) := hg.implicitFunction_apply_self (by simp) hinv
  have hge : ∀ᶠ q in 𝓝 (s, ℓ), supportEquations F (q, ψ q) = 0 := by
    have hh := hg.eventually_apply_implicitFunction (by simp) hinv
    have hg0 : supportEquations F ((s, ℓ), (z, lam)) = 0 := by
      simp [supportEquations, fiberGradient, hzF, hder]
    simpa only [hg0, ψ] using hh
  have hnearW : ∀ᶠ q in 𝓝 (s, ℓ), (q.1, (ψ q).1) ∈ W := by
    apply (continuousAt_fst.prodMk hψ.continuousAt.fst).eventually
      (hW.mem_nhds (show ((s, ℓ).1, (ψ (s, ℓ)).1) ∈ W by simpa [hψ₀] using hz))
  have hnearL : ∀ᶠ q in 𝓝 (s, ℓ), 0 < (ψ q).2 := by
    exact hψ.continuousAt.snd.eventually (eventually_gt_nhds (by simpa [hψ₀] using hlam))
  have hnearB : ∀ᶠ q in 𝓝 (s, ℓ), q.1 ∈ B :=
    continuousAt_fst.eventually (hB.mem_nhds hs)
  have heq : (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ W ∧ F (q.1, y) ≤ 0} q.2) =ᶠ[𝓝 (s, ℓ)]
      (fun q => q.2 ((ψ q).1)) := by
    filter_upwards [hge, hnearW, hnearL, hnearB] with q hq hqW hqL hqB
    have hzero : F (q.1, (ψ q).1) = 0 := congrArg Prod.fst hq
    have hgrad : fiberGradient F (q.1, (ψ q).1) = (ψ q).2 • q.2 :=
      sub_eq_zero.mp (congrArg Prod.snd hq)
    apply supportValue_of_equations (hcv q.1 hqB) hqW hzero _ hqL hgrad
    exact ((hF.contDiffAt (hW.mem_nhds hqW)).comp _
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  exact (contDiffAt_snd.clm_apply hψ.fst).congr_of_eventuallyEq heq

/- Finiteness of the literal support value on a compact fiber. -/
theorem le_supportValue {K : Set E} (hK : IsCompact K) {z : E} (hz : z ∈ K)
    (ℓ : E →L[ℝ] ℝ) : ℓ z ≤ supportValue K ℓ := by
  exact le_csSup (hK.image ℓ.continuous).bddAbove ⟨z, hz, rfl⟩

/- The envelope identity recovers the Gauss parametrization from the literal
support function; no choice of a surrogate support coordinate is involved. -/

theorem supportValue_pos [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K)
    (hzero : (0 : E) ∈ interior K) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    0 < supportValue K ℓ := by
  have hex : ∃ v : E, ℓ v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hℓ
    ext v
    exact hn v
  obtain ⟨v, hv⟩ := hex
  let w := (ℓ v) • v
  have hw : 0 < ℓ w := by simp only [w, map_smul, smul_eq_mul]; exact mul_self_pos.mpr hv
  have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  let t := r / (2 * ‖w‖)
  have ht : 0 < t := div_pos hr (by positivity)
  have htw : t • w ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    have hh : r / (2 * ‖w‖) * ‖w‖ = r / 2 := by field_simp
    rw [hh]
    linarith
  have hp : 0 < ℓ (t • w) := by simpa using mul_pos ht hw
  exact hp.trans_le (le_supportValue hK htw ℓ)

end SupportGeometry

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/

end CompleteSphericalDependencies

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A genuine affine slice of the original epigraph, in arbitrary transverse
coordinates. -/
theorem affineEpigraphFiber_no_vertical {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {x : Space n} {z : ℝ} {A : E →L[ℝ] Space n}
    {b : E →L[ℝ] ℝ} (hK : IsCompact (affineEpigraphFiber Ω u x z A b))
    (hne : (affineEpigraphFiber Ω u x z A b).Nonempty)
    {v : E} (hv : A v = 0) : b v = 0 := by
  by_contra hb
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨M, hM⟩ := (hK.image b.continuous).bddAbove
  let r := max M (u (x + A y₀) - z) + 1
  let t := (r - b y₀) / b v
  have hbase : x + A (y₀ + t • v) = x + A y₀ := by simp [hv]
  have hheight : b (y₀ + t • v) = r := by
    simp only [map_add, map_smul, smul_eq_mul, t]
    field_simp
    ring
  have hy : y₀ + t • v ∈ affineEpigraphFiber Ω u x z A b := by
    refine ⟨by rw [hbase]; exact hy₀.1, ?_⟩
    rw [hbase, hheight]
    have hh := le_max_right M (u (x + A y₀) - z)
    dsimp [r]
    linarith
  have hh := hM (show b (y₀ + t • v) ∈ b '' affineEpigraphFiber Ω u x z A b from
    ⟨_, hy, rfl⟩)
  rw [hheight] at hh
  have hh' := le_max_left M (u (x + A y₀) - z)
  dsimp [r] at hh
  linarith

/- For an affine coordinate isomorphism compact fibers force injectivity of
its horizontal linear part. -/
theorem affineEpigraphFiber_injective {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {x : Space n} {z : ℝ} {A : E →L[ℝ] Space n}
    {b : E →L[ℝ] ℝ} (hK : IsCompact (affineEpigraphFiber Ω u x z A b))
    (hne : (affineEpigraphFiber Ω u x z A b).Nonempty)
    (hi : Function.Injective (fun y => (A y, b y))) : Function.Injective A := by
  intro v w hvw
  have hav : A (v - w) = 0 := by simpa [map_sub] using sub_eq_zero.mpr hvw
  have hb := affineEpigraphFiber_no_vertical hK hne hav
  have hbw : b v = b w := sub_eq_zero.mp (by simpa [map_sub] using hb)
  exact hi (Prod.ext hvw hbw)

/- Chain rule for the actual second differential of an affine epigraph slice. -/
theorem affineSlice_second {n : ℕ} {u : Space n → ℝ} {x : Space n} {z : ℝ}
    {A : E →L[ℝ] Space n} {b : E →L[ℝ] ℝ} {y : E}
    (hu : ContDiffAt ℝ ∞ u (x + A y)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => u (x + A q) - (z + b q))) y v w =
      fderiv ℝ (fderiv ℝ u) (x + A y) (A v) (A w) := by
  have he : fderiv ℝ (fun q => u (x + A q) - (z + b q)) =ᶠ[𝓝 y]
      (fun q => (fderiv ℝ u (x + A q)).comp A - b) := by
    have hne : ∀ᶠ q in 𝓝 y, DifferentiableAt ℝ u (x + A q) := by
      apply (continuous_const.add A.continuous).continuousAt.eventually
      have hh : ∀ᶠ p in 𝓝 (x + A y), ContDiffAt ℝ 1 u p :=
        (hu.of_le (by simp)).eventually (by simp)
      exact hh.mono (fun p hp => hp.differentiableAt (by simp))
    filter_upwards [hne] with q hq
    exact ((hq.hasFDerivAt.comp q (A.hasFDerivAt.const_add x)).sub
      (b.hasFDerivAt.const_add z)).fderiv
  rw [he.fderiv_eq]
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hc := (hd.comp y (A.hasFDerivAt.const_add x)).clm_comp (hasFDerivAt_const A y)
  have heq := (hc.sub_const b).fderiv
  simp only [Function.comp_def] at heq
  rw [heq]
  simp

/- An interior point of a convex sublevel is a strict sublevel point whenever
its actual Hessian is positive definite. -/
theorem sublevel_interior_strict [Nontrivial E] {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {z : E}
    (hz : z ∈ interior {y | y ∈ W ∧ F y ≤ 0})
    (hd : DifferentiableAt ℝ F z)
    (hH : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ F) z v v) : F z < 0 := by
  have hzK := interior_subset hz
  by_contra hn
  have hz0 : F z = 0 := le_antisymm hzK.2 (le_of_not_gt hn)
  have hnK : {y | y ∈ W ∧ F y ≤ 0} ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  have hm : IsLocalMax F z := by
    filter_upwards [hnK] with y hy
    simpa [hz0] using hy.2
  have hdz := hm.fderiv_eq_zero
  have he : F =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnK] with y hy
    have hh := convex_first_order hcv hzK.1 hy.1 hd
    simp only [hdz, zero_apply, hz0, sub_zero] at hh
    exact le_antisymm hy.2 hh
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hh := hH v hv
  rw [he.fderiv.fderiv_eq] at hh
  simp at hh

/- Convexity survives the actual affine slice and subtraction of its height. -/
theorem convexOn_affineSlice {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hcv : ConvexOn ℝ Ω u) (x : Space n) (z : ℝ)
    (A : E →L[ℝ] Space n) (b : E →L[ℝ] ℝ) :
    ConvexOn ℝ {y | x + A y ∈ Ω} (fun y => u (x + A y) - (z + b y)) := by
  let g : E →ᵃ[ℝ] Space n :=
    { toFun := fun y => x + A y
      linear := A.toLinearMap
      map_vadd' := by
        intro v p
        change x + A (p + v) = A p + (x + A v)
        rw [map_add]
        abel }
  have hc := hcv.comp_affineMap g
  have hb := (b.toLinearMap.concaveOn hc.1).add_const z
  have hh := hc.sub hb
  change ConvexOn ℝ {y | x + A y ∈ Ω} (fun y => u (x + A y) - (b y + z)) at hh
  simpa only [add_comm (b _) z] using hh

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- The literal inverse image of the original epigraph under affine coordinates. -/

theorem affine_coordinates_split {n : ℕ} (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (s : S) (y : E) :
    a + L (s, y) = ((a + L (s, 0)).1 + affineFiberHorizontal L y,
      (a + L (s, 0)).2 + affineFiberHeight L y) := by
  have hh : L (s, y) = L (s, 0) + L (0, y) := by rw [← map_add]; simp
  rw [hh]
  ext <;> simp [affineFiberHorizontal, affineFiberHeight, add_assoc]

theorem affineEpigraphPullback_fiber {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (s : S) :
    {y | (s, y) ∈ affineEpigraphPullback Ω u a L} =
      affineEpigraphFiber Ω u (a + L (s, 0)).1 (a + L (s, 0)).2
        (affineFiberHorizontal L) (affineFiberHeight L) := by
  ext y
  change ((a + L (s, y)).1 ∈ Ω ∧ u (a + L (s, y)).1 ≤ (a + L (s, y)).2) ↔ _
  rw [affine_coordinates_split a L s y]
  rfl

theorem affineFiberHorizontal_injective {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {a : Space n × ℝ} {L : (S × E) ≃L[ℝ] (Space n × ℝ)} {s : S}
    (hK : IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hne : {y | (s, y) ∈ affineEpigraphPullback Ω u a L}.Nonempty) :
    Function.Injective (affineFiberHorizontal L) := by
  rw [affineEpigraphPullback_fiber] at hK hne
  apply affineEpigraphFiber_injective hK hne
  intro v w hvw
  have hh : L (0, v) = L (0, w) := hvw
  exact congrArg Prod.snd (L.injective hh)

variable [CompleteSpace S]

/- The principal support-coordinate regularity assertion in tubes.tex:39–60,
for actual affine images of the standing epigraph, not abstract smooth bodies.
The transverse dimension is nonzero, as in the manuscript (m=n+1-k≥1). -/
theorem affineEpigraph_support_smooth [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ affineEpigraphPullback Ω u a L} q.2) (s, ℓ) ∧
    0 < supportValue {y | (s, y) ∈ affineEpigraphPullback Ω u a L} ℓ := by
  let W : Set (S × E) := {p | (a + L p).1 ∈ Ω}
  let F : S × E → ℝ := fun p => u (a + L p).1 - (a + L p).2
  have hbase : ContDiff ℝ ∞ (fun p : S × E => (a + L p).1) :=
    (contDiff_const.add L.contDiff).fst
  have hheight : ContDiff ℝ ∞ (fun p : S × E => (a + L p).2) :=
    (contDiff_const.add L.contDiff).snd
  have hW : IsOpen W := hΩ.preimage hbase.continuous
  have hF : ContDiffOn ℝ ∞ F W :=
    (hu.comp hbase.contDiffOn (fun _ h => h)).sub hheight.contDiffOn
  have hFu : ConvexOn ℝ Ω u :=
    convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hFeq (r : S) : (fun q => F (r, q)) = (fun q =>
      u ((a + L (r, 0)).1 + affineFiberHorizontal L q) -
        ((a + L (r, 0)).2 + affineFiberHeight L q)) := by
    funext q
    change u (a + L (r, q)).1 - (a + L (r, q)).2 = _
    rw [affine_coordinates_split a L r q]
  have hWeq (r : S) : {y | (r, y) ∈ W} =
      {y | (a + L (r, 0)).1 + affineFiberHorizontal L y ∈ Ω} := by
    ext y
    change (a + L (r, y)).1 ∈ Ω ↔ _
    rw [affine_coordinates_split a L r y]
    rfl
  have hcvF (r : S) : ConvexOn ℝ {y | (r, y) ∈ W} (fun y => F (r, y)) := by
    rw [hFeq, hWeq]
    exact convexOn_affineSlice hFu (a + L (r, 0)).1 (a + L (r, 0)).2
      (affineFiberHorizontal L) (affineFiberHeight L)
  have hKeq (r : S) : {y | (r, y) ∈ W ∧ F (r, y) ≤ 0} =
      {y | (r, y) ∈ affineEpigraphPullback Ω u a L} := by
    ext y
    simp only [W, F, affineEpigraphPullback, mem_ofPred_eq, sub_nonpos]
  have hK' : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by rw [hKeq]; exact hK s hs
  have hzero' : (0 : E) ∈ interior {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by
    rw [hKeq]; exact hzero s hs
  have hA : Function.Injective (affineFiberHorizontal L) :=
    affineFiberHorizontal_injective (hK s hs) ⟨0, interior_subset (hzero s hs)⟩
  have hH (y : E) (hy : (s, y) ∈ W) (v : E) (hv : v ≠ 0) :
      0 < fderiv ℝ (fderiv ℝ (fun q => F (s, q))) y v v := by
    have huc := hu.contDiffAt (hΩ.mem_nhds hy)
    have hx : (a + L (s, y)).1 = (a + L (s, 0)).1 + affineFiberHorizontal L y :=
      congrArg Prod.fst (affine_coordinates_split a L s y)
    rw [hFeq, affineSlice_second (by rw [← hx]; exact huc)]
    exact second_fderiv_pos (by rw [← hx]; exact huc)
      (by rw [← hx]; exact hp _ hy)
      (fun hh => hv (hA (by simpa using hh)))
  have hzW : (s, (0 : E)) ∈ W := (interior_subset hzero').1
  have hzF : F (s, 0) < 0 := sublevel_interior_strict (hcvF s) hzero'
    (((hF.contDiffAt (hW.mem_nhds hzW)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) (hH 0 hzW)
  have hh := contDiffAt_supportValue_fibers hB hW hF (fun r _ => hcvF r)
    hs hzW hzF hK' (fun y hy _ => hH y hy) hℓ
  refine ⟨?_, supportValue_pos (hK s hs) (hzero s hs) hℓ⟩
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  rw [hKeq]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GaussCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/- The one-homogeneous extension of the literal spherical support function. -/

theorem homogeneousSupport_le {K : Set E} (hK : IsCompact K)
    {z : E} (hz : z ∈ K) (e : E) : inner ℝ e z ≤ homogeneousSupport K e :=
  le_supportValue hK hz (InnerProductSpace.toDual ℝ E e)

theorem homogeneousSupport_eq_of_max {K : Set E} {e z : E}
    (hz : z ∈ K) (hm : IsMaxOn (fun y => inner ℝ e y) K z) :
    homogeneousSupport K e = inner ℝ e z := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨inner ℝ e z, z, hz, rfl⟩
  · rintro r ⟨y, hy, rfl⟩; exact hm hy
  · intro r hr; exact ⟨inner ℝ e z, ⟨z, hz, rfl⟩, hr⟩

theorem gaussPoint_eq_of_max {K : Set E} (hK : IsCompact K)
    {e z : E} (hz : z ∈ K) (hm : homogeneousSupport K e = inner ℝ e z)
    (hd : DifferentiableAt ℝ (homogeneousSupport K) e) : gaussPoint K e = z := by
  have hl : IsLocalMin (fun q => homogeneousSupport K q - inner ℝ z q) e := by
    apply Eventually.of_forall
    intro q
    have hh := homogeneousSupport_le hK hz q
    simpa [real_inner_comm z, hm] using sub_nonneg.mpr hh
  have hder := hd.hasFDerivAt.sub (InnerProductSpace.toDual ℝ E z).hasFDerivAt
  have hh : fderiv ℝ (homogeneousSupport K) e - InnerProductSpace.toDual ℝ E z = 0 := by
    rw [← hder.fderiv]
    exact hl.fderiv_eq_zero
  unfold gaussPoint gradient
  rw [sub_eq_zero.mp hh]
  simp

theorem gaussPoint_mem_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {e : E} (hd : DifferentiableAt ℝ (homogeneousSupport K) e) :
    gaussPoint K e ∈ K ∧
      homogeneousSupport K e = inner ℝ e (gaussPoint K e) := by
  obtain ⟨z, hz, hm⟩ := hK.exists_isMaxOn hne (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  have he := homogeneousSupport_eq_of_max hz hm
  rw [gaussPoint_eq_of_max hK hz he hd]
  exact ⟨hz, he⟩

theorem homogeneousSupport_euler {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {e : E} (hd : DifferentiableAt ℝ (homogeneousSupport K) e) :
    fderiv ℝ (homogeneousSupport K) e e = homogeneousSupport K e := by
  have hh := (gaussPoint_mem_support hK hne hd).2
  rw [real_inner_comm] at hh
  simpa [gaussPoint, gradient] using hh.symm

/- Euler's identity differentiates to the radial null direction of the support
Hessian. This is the ambient version of the spherical radius matrix. -/
theorem homogeneousSupport_hessian_radial {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {e : E} (hh : ContDiffAt ℝ ∞ (homogeneousSupport K) e)
    (v : E) : fderiv ℝ (fderiv ℝ (homogeneousSupport K)) e v e = 0 := by
  have hd := hh.differentiableAt (by simp)
  have hdd := (hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : (fun q => fderiv ℝ (homogeneousSupport K) q q) =ᶠ[𝓝 e]
      homogeneousSupport K := by
    filter_upwards [(hh.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact homogeneousSupport_euler hK hne (hq.differentiableAt (by norm_num))
  have hr := hdd.hasFDerivAt.clm_apply (hasFDerivAt_id e)
  have heq := (hr.congr_of_eventuallyEq he.symm).unique hd.hasFDerivAt
  have hev := congrArg (fun f : E →L[ℝ] ℝ => f v) heq
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, id_eq] at hev
  linarith

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

omit [CompleteSpace S] in
theorem contDiffAt_gaussPoint_fibers {K : S → Set E} {s : S} {e : E}
    (hh : ContDiffAt ℝ ∞ (fun p : S × E => homogeneousSupport (K p.1) p.2) (s,e)) :
    ContDiffAt ℝ ∞ (fun p : S × E => gaussPoint (K p.1) p.2) (s,e) := by
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt).comp
    (s,e) (contDiffAt_fiberGradient hh)

omit [CompleteSpace S] in
theorem contDiffAt_homogeneousSupport_fibers {K : S → Set E} {s : S} {e : E}
    (hh : ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) => supportValue (K q.1) q.2)
      (s, InnerProductSpace.toDual ℝ E e)) :
    ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) := by
  have hc : ContDiffAt ℝ ∞ (fun q : S × E =>
      (q.1, InnerProductSpace.toDual ℝ E q.2)) (s,e) :=
    contDiffAt_fst.prodMk
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.contDiff.contDiffAt.comp
        (s,e) contDiffAt_snd)
  have ht := hh.comp (s,e) hc
  exact ht

/- Actual smooth Gauss coordinates of each affine epigraph tube. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JetCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem second_fderiv_comp {f : F → G} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) +
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hdf := hf.differentiableAt (by simp)
  have hdg := hg.differentiableAt (by simp)
  have hddf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hddg := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hdfg := (((hf.comp x hg).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
  have hleft := hdfg.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hright := (hddf.hasFDerivAt.comp x hdg.hasFDerivAt).clm_apply
    (hddg.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have heq : (fun q => fderiv ℝ (f ∘ g) q w) =ᶠ[𝓝 x]
      (fun q => fderiv ℝ f (g q) (fderiv ℝ g q w)) := by
    have hfg : ∀ᶠ q in 𝓝 x, ContDiffAt ℝ 1 f (g q) := hg.continuousAt.eventually
      ((hf.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp))
    filter_upwards [hfg,
      (hg.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqf hqg
    rw [fderiv_comp q (hqf.differentiableAt (by norm_num)) (hqg.differentiableAt (by norm_num))]
    rfl
  have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hh := congrArg (fun L : E →L[ℝ] G => L v) he
  simpa [add_comm] using hh

theorem second_fderiv_clm_comp (L : F →L[ℝ] G) {Y : E → F} {x : E}
    (hY : ContDiffAt ℝ ∞ Y x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => L (Y q))) x v w =
      L (fderiv ℝ (fderiv ℝ Y) x v w) := by
  have hh := second_fderiv_comp L.contDiff.contDiffAt hY v w
  have hdL : fderiv ℝ (L : F → G) = (fun _ => L) := funext (fun _ => L.fderiv)
  rw [hdL] at hh
  simpa only [fderiv_const_apply, zero_apply, zero_add, Function.comp_def] using hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma homogeneousSupport_fibers_angular {K : S → Set E} {x : S × E}
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x)
    (w : E) :
    fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x (0,w) =
      inner ℝ (gaussPoint (K x.1) x.2) w := by
  have hd := hH.hasFDerivAt.comp (f := fun y : E => (x.1,y)) x.2
    ((hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2))
  have he : fderiv ℝ (homogeneousSupport (K x.1)) x.2 w =
      fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x (0,w) := by
    change fderiv ℝ ((fun q : S × E => homogeneousSupport (K q.1) q.2) ∘
      (fun y : E => (x.1,y))) x.2 w = _
    rw [hd.fderiv]
    rfl
  rw [← he]
  simp [gaussPoint]

lemma homogeneousSupport_fibers_euler {K : S → Set E} {x : S × E}
    (hK : IsCompact (K x.1)) (hne : (K x.1).Nonempty)
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x) :
    homogeneousSupport (K x.1) x.2 = inner ℝ x.2 (gaussPoint (K x.1) x.2) := by
  exact (gaussPoint_mem_support hK hne
    (hH.comp (f := fun y : E => (x.1,y)) x.2 (differentiableAt_const x.1 |>.prodMk differentiableAt_id))).2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeDensityVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

lemma second_fderiv_affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} (L : S →L[ℝ] F) (a : F)
    {x : S} (hf : ContDiffAt ℝ ∞ f (a + L x)) (v w : S) :
    fderiv ℝ (fderiv ℝ (fun z => f (a + L z))) x v w =
      fderiv ℝ (fderiv ℝ f) (a + L x) (L v) (L w) := by
  have hd (z : S) : fderiv ℝ (fun z => a + L z) z = L := by
    exact ((L.hasFDerivAt).const_add a).fderiv
  have hdd : fderiv ℝ (fderiv ℝ (fun z => a + L z)) x = 0 := by
    rw [show fderiv ℝ (fun z => a + L z) = (fun _ => L) from funext hd]
    simp
  change fderiv ℝ (fderiv ℝ (f ∘ (fun z => a + L z))) x v w = _
  rw [second_fderiv_comp (g := fun z => a + L z) hf (contDiffAt_const.add L.contDiff.contDiffAt), hd, hdd]
  simp

lemma second_fderiv_prod_right {H : S × E → ℝ} {s : S} {e : E}
    (hH : ContDiffAt ℝ ∞ H (s,e)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v w =
      fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,w) := by
  simpa using second_fderiv_affine_comp (ContinuousLinearMap.inr ℝ S E) (s,0) (by simpa using hH) v w

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineEpigraph_support_jets {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ContDiffAt ℝ ∞ H (s,e) ∧ ContDiffAt ℝ ∞ Y (s,e) ∧
      H =ᶠ[𝓝 (s,e)] (fun q => inner ℝ q.2 (Y q)) ∧
      ∀ᶠ q in 𝓝 (s,e), ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w := by
  let K : S → Set E := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L}
  let H : S × E → ℝ := fun q => homogeneousSupport (K q.1) q.2
  let Y : S × E → E := fun q => gaussPoint (K q.1) q.2
  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz; apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  have hH : ContDiffAt ℝ ∞ H (s,e) := contDiffAt_homogeneousSupport_fibers
    (K := K) (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hs hℓ).1
  refine ⟨hH, contDiffAt_gaussPoint_fibers (K := K) hH, ?_, ?_⟩
  · filter_upwards [(continuous_fst.continuousAt.preimage_mem_nhds (hB.mem_nhds hs)),
      (hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqs hq
    exact homogeneousSupport_fibers_euler (hK q.1 hqs) ⟨0, interior_subset (hzero q.1 hqs)⟩
      (hq.differentiableAt (by norm_num))
  · filter_upwards [(hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact homogeneousSupport_fibers_angular (hq.differentiableAt (by norm_num))

/- Both matrices in the actual tube area formula are positive definite,
including an empty angular matrix. This is derived from the original graph,
not imposed as an additional curvature assumption. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatBlockCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiffAt_adjugate_entries {A : E → Matrix ι ι ℝ} {x : E}
    (hA : ContDiffAt ℝ ∞ (fun y i j => A y i j) x) (i j : ι) :
    ContDiffAt ℝ ∞ (fun y => (A y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  change ContDiffAt ℝ ∞ (fun y => continuousDetRows (fun l m => (A y).updateRow j (Pi.single i 1) l m)) x
  apply (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x
  apply contDiffAt_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simpa only [Matrix.updateRow_self] using (contDiffAt_const (c := (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simp only [Matrix.updateRow_ne hl]
    exact (contDiffAt_pi.mp hA) l

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BlockNewton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section BlockNewton
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adjugate_fromBlocks_scalar (A : Matrix ι ι ℝ) (t : ℝ) (i j : ι) :
    (Matrix.fromBlocks A 0 0 (t • (1 : Matrix Unit Unit ℝ))).adjugate
      (Sum.inl i) (Sum.inl j) = t * A.adjugate i j := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  have hh : (Matrix.fromBlocks A 0 0 (t • (1 : Matrix Unit Unit ℝ))).updateRow
      (Sum.inl j) (Pi.single (Sum.inl i) 1) =
      Matrix.fromBlocks (A.updateRow j (Pi.single i 1)) 0 0 (t • (1 : Matrix Unit Unit ℝ)) := by
    ext l m
    cases l with
    | inl l =>
      cases m with
      | inl m => simp [Matrix.updateRow_apply, Pi.single_apply, Matrix.fromBlocks]
      | inr m => simp [Matrix.updateRow_apply, Matrix.fromBlocks]
    | inr l =>
      cases m <;> simp [Matrix.updateRow_apply, Matrix.fromBlocks]
  rw [hh, Matrix.det_fromBlocks_zero₂₁]
  simp [mul_comm]

end BlockNewton
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adjugate_eq_det_smul_transpose {Q : Matrix ι ι ℝ} (hQ : Q * Qᵀ = 1) :
    Q.adjugate = Q.det • Qᵀ := by
  calc
    Q.adjugate = Q.adjugate * (Q * Qᵀ) := by rw [hQ, Matrix.mul_one]
    _ = (Q.adjugate * Q) * Qᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = Q.det • Qᵀ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

lemma adjugate_conjugate_orthogonal {Q : Matrix ι ι ℝ}
    (hQ : Q * Qᵀ = 1) (hQt : Qᵀ * Q = 1) (A : Matrix ι ι ℝ) :
    (Qᵀ * A * Q).adjugate = Qᵀ * A.adjugate * Q := by
  have hd : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using hh
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    adjugate_eq_det_smul_transpose hQ,
    adjugate_eq_det_smul_transpose (Q := Qᵀ) (by simpa using hQt),
    Matrix.transpose_transpose, Matrix.det_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, one_smul, Matrix.mul_assoc]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_RadialAdjugate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adjugate_block_radial (R : Matrix ι ι ℝ) :
    (Matrix.fromBlocks R 0 0 (0 : Matrix Unit Unit ℝ)).adjugate =
      Matrix.fromBlocks 0 0 0 (R.det • (1 : Matrix Unit Unit ℝ)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := adjugate_fromBlocks_scalar R 0 i j
      simpa using hh
    | inr j =>
      cases j
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_column_eq_zero (Sum.inr ())
      intro l
      cases l <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
  | inr i =>
    cases i
    cases j with
    | inl j =>
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inr ())
      intro l
      cases l <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
    | inr j =>
      cases j
      rw [Matrix.adjugate_apply]
      have hh : (Matrix.fromBlocks R 0 0 (0 : Matrix Unit Unit ℝ)).updateRow
          (Sum.inr ()) (Pi.single (Sum.inr ()) 1) = Matrix.fromBlocks R 0 0 (1 : Matrix Unit Unit ℝ) := by
        ext l m
        cases l <;> cases m <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
      rw [hh,Matrix.det_fromBlocks_zero₂₁]
      simp

lemma radialShear_det (e : ι ⊕ Unit → ℝ) : (radialShear e).det = 1 := by
  rw [radialShear,Matrix.det_fromBlocks_zero₂₁]
  simp

omit [Fintype ι] in
lemma radialShear_last (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1) (i : ι ⊕ Unit) :
    radialShear e i (Sum.inr ()) = e i := by
  cases i <;> simp [radialShear,Matrix.fromBlocks,he]

lemma mul_radialShear_left (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (i : ι ⊕ Unit) (j : ι) :
    (A * radialShear e) i (Sum.inl j) = A i (Sum.inl j) := by
  simp [Matrix.mul_apply,Fintype.sum_sum_type,radialShear,Matrix.fromBlocks,Matrix.one_apply]

lemma transpose_radialShear_mul_left (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (i : ι) (j : ι ⊕ Unit) :
    ((radialShear e)ᵀ * A) (Sum.inl i) j = A (Sum.inl i) j := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type,radialShear,
    Matrix.fromBlocks,Matrix.one_apply]

lemma mul_radialShear_last (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1) (i : ι ⊕ Unit) :
    (A * radialShear e) i (Sum.inr ()) = (A *ᵥ e) i := by
  simp only [Matrix.mul_apply,radialShear_last e he,Matrix.mulVec, dotProduct]

lemma radialShear_conjugate {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) :
    (radialShear e)ᵀ * A * radialShear e =
      Matrix.fromBlocks (A.submatrix Sum.inl Sum.inl) 0 0 (0 : Matrix Unit Unit ℝ) := by
  have hs : ((radialShear e)ᵀ * A * radialShear e).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.transpose_mul,Matrix.transpose_transpose,hA.eq,Matrix.mul_assoc]
  have hlast (i : ι ⊕ Unit) : ((radialShear e)ᵀ * A * radialShear e) i (Sum.inr ()) = 0 := by
    rw [Matrix.mul_assoc,Matrix.mul_apply]
    simp [mul_radialShear_last A e he,hz]
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [Matrix.mul_assoc,transpose_radialShear_mul_left,mul_radialShear_left]
      rfl
    | inr j => cases j; exact hlast _
  | inr i =>
    cases i
    cases j with
    | inl j => rw [← hs.apply]; exact hlast _
    | inr j => cases j; exact hlast _

/- A symmetric form with radial null vector has its full adjugate equal to
its transverse principal minor times the radial outer product. This includes
all empty transverse blocks and needs no invertibility of the full matrix. -/
theorem radial_adjugate {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) (i j : ι ⊕ Unit) :
    A.adjugate i j = (A.submatrix Sum.inl Sum.inl).det * e i * e j := by
  let P := radialShear e
  let d := (A.submatrix Sum.inl Sum.inl).det
  have hP : P.det = 1 := radialShear_det e
  have hp : P * P.adjugate = 1 := by rw [Matrix.mul_adjugate,hP,one_smul]
  have hpt : (Pᵀ).adjugate * Pᵀ = 1 := by
    rw [Matrix.adjugate_mul,Matrix.det_transpose,hP,one_smul]
  have hh := congrArg Matrix.adjugate (radialShear_conjugate hA e he hz)
  rw [adjugate_block_radial,Matrix.adjugate_mul_distrib,Matrix.adjugate_mul_distrib] at hh
  have hmul := congrArg (fun M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ => P*M*Pᵀ) hh
  change P * (P.adjugate * (A.adjugate * (Pᵀ).adjugate)) * Pᵀ =
    P*Matrix.fromBlocks 0 0 0 (d • (1 : Matrix Unit Unit ℝ))*Pᵀ at hmul
  have heq : A.adjugate = P*Matrix.fromBlocks 0 0 0 (d • (1 : Matrix Unit Unit ℝ))*Pᵀ := by
    calc
      _ = (P*P.adjugate)*A.adjugate*((Pᵀ).adjugate*Pᵀ) := by rw [hp,hpt,Matrix.one_mul,Matrix.mul_one]
      _ = _ := by simpa only [Matrix.mul_assoc] using hmul
  rw [heq]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,zero_add,
    Fintype.sum_unique,Matrix.smul_apply,Matrix.one_apply,ite_true,smul_eq_mul,mul_one]
  change (P i (Sum.inr ()) * d)*P j (Sum.inr ()) = _
  dsimp only [P,d]
  rw [radialShear_last e he,radialShear_last e he]
  ring

lemma radial_adjugate_trace {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) :
    A.adjugate.trace = (A.submatrix Sum.inl Sum.inl).det * ∑ i, e i * e i := by
  simp only [Matrix.trace,Matrix.diag,radial_adjugate hA e he hz,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma homogeneousSupport_smul {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (e : E) {c : ℝ} (hc : 0 < c) :
    homogeneousSupport K (c • e) = c * homogeneousSupport K e := by
  obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn hne
    (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  rw [homogeneousSupport_eq_of_max hz hm]
  have hmc : IsMaxOn (fun y => inner ℝ (c • e) y) K z := by
    intro y hy
    change inner ℝ (c • e) y ≤ inner ℝ (c • e) z
    simp only [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (hm hy) hc.le
  rw [homogeneousSupport_eq_of_max hz hmc,real_inner_smul_left]

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [CompleteSpace E] in
lemma second_fderiv_const_mul {H : S × E → ℝ} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (c : ℝ) (v w : S × E) :
    fderiv ℝ (fderiv ℝ (fun q => c * H q)) x v w =
      c * fderiv ℝ (fderiv ℝ H) x v w := by
  have hh : (fun q => c * H q) = (c • ContinuousLinearMap.id ℝ ℝ) ∘ H := by
    ext q
    simp
  rw [hh]
  simpa [Function.comp_def] using second_fderiv_clm_comp
    (c • ContinuousLinearMap.id ℝ ℝ) hH v w

lemma homogeneous_fiber_hessian_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (v w : S × E) :
    fderiv ℝ (fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2))
      (s,c • e) (normalScale c v) (normalScale c w) =
    c * fderiv ℝ (fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2)) (s,e) v w := by
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have he : (fun q => H (normalScale c q)) =ᶠ[𝓝 (s,e)] (fun q => c * H q) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hD.mem_nhds hs)] with q hq
    exact homogeneousSupport_smul (hK _ hq) (hne _ hq) q.2 hc
  have hh := congrArg (fun A : (S × E) →L[ℝ] (S × E) →L[ℝ] ℝ => A v w)
    ((he.fderiv (𝕜 := ℝ)).fderiv_eq)
  rw [second_fderiv_const_mul hH] at hh
  have hj := second_fderiv_affine_comp (normalScale (S := S) c) (0 : S × E)
    (x := (s,e)) (by simpa using hHc) v w
  simp only [zero_add] at hj
  exact hj.symm.trans hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section NewtonBasis
open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace E] in
lemma orthogonalChange_transpose_mul (b c : OrthonormalBasis ι ℝ E) :
    (orthogonalChange b c)ᵀ * orthogonalChange b c = 1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,orthogonalChange,Matrix.of_apply,Matrix.one_apply]
  calc
    ∑ k, inner ℝ (b k) (c i) * inner ℝ (b k) (c j) = inner ℝ (c i) (c j) := by
      convert b.sum_inner_mul_inner (c i) (c j) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_comm (b k) (c i)]
    _ = _ := orthonormal_iff_ite.mp c.orthonormal i j

omit [CompleteSpace E] in
lemma orthogonalChange_mul_transpose (b c : OrthonormalBasis ι ℝ E) :
    orthogonalChange b c * (orthogonalChange b c)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,orthogonalChange,Matrix.of_apply,Matrix.one_apply]
  calc
    ∑ k, inner ℝ (b i) (c k) * inner ℝ (b j) (c k) = inner ℝ (b i) (b j) := by
      convert c.sum_inner_mul_inner (b i) (b j) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_comm (b j) (c k)]
    _ = _ := orthonormal_iff_ite.mp b.orthonormal i j

end NewtonBasis
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_change (H : S × E → ℝ) (q : S × E)
    (b c : OrthonormalBasis ι ℝ E) :
    tubeFullRadiusMatrix H q c =
      (orthogonalChange b c)ᵀ * tubeFullRadiusMatrix H q b * orthogonalChange b c := by
  have hre (v : E) : ((0:S),v) = ∑ i, b.repr v i • (0,b i) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' v).symm
  ext i j
  simp only [tubeFullRadiusMatrix,Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,
    orthogonalChange,Finset.sum_mul]
  conv_lhs => rw [hre (c i),hre (c j)]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum,
    OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [CompleteSpace E] in
lemma tubeAngularDensity_basis_independent (H : S × E → ℝ) (q : S × E)
    (b c : OrthonormalBasis ι ℝ E) : tubeAngularDensity H q c = tubeAngularDensity H q b := by
  rw [tubeAngularDensity,tubeFullRadiusMatrix_change H q b c,
    adjugate_conjugate_orthogonal (orthogonalChange_mul_transpose b c)
      (orthogonalChange_transpose_mul b c),Matrix.trace_mul_cycle,
      orthogonalChange_mul_transpose,Matrix.one_mul]
  rfl

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_symm {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    (tubeFullRadiusMatrix H q b).IsSymm := by
  have hh := hH.isSymmSndFDerivAt (by simp)
  ext i j
  exact hh.eq _ _

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_radial {H : S × E → ℝ} {q : S × E}
    (b : OrthonormalBasis ι ℝ E)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0) :
    tubeFullRadiusMatrix H q b *ᵥ (b.repr q.2) = 0 := by
  ext i
  have hh := hr (b i)
  have he : ((0:S),q.2) = ∑ j, b.repr q.2 j • (0,b j) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' q.2).symm
  rw [he] at hh
  simp only [map_sum,map_smul,smul_eq_mul] at hh
  simpa [Matrix.mulVec,dotProduct,tubeFullRadiusMatrix,map_sum,map_smul,mul_comm] using hh

/- The full cofactor trace recovers the transverse determinant in every flat
normal chart. No unit-normal constraint is imposed away from the chart center. -/
omit [CompleteSpace E] in
lemma tubeAngularDensity_flat {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : inner ℝ q.2 (b (Sum.inr ())) = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0) :
    tubeAngularDensity H q b = (tubeRadiusMatrix H q b).det * inner ℝ q.2 q.2 := by
  have hc : b.repr q.2 (Sum.inr ()) = 1 := by
    simpa [OrthonormalBasis.repr_apply_apply,real_inner_comm] using he
  have hh := radial_adjugate_trace (tubeFullRadiusMatrix_symm hH b)
    (b.repr q.2) hc (tubeFullRadiusMatrix_radial b hr)
  change tubeAngularDensity H q b = (tubeRadiusMatrix H q b).det * _ at hh
  rw [← b.sum_inner_mul_inner q.2 q.2]
  simpa [OrthonormalBasis.repr_apply_apply,real_inner_comm q.2] using hh

omit [Fintype ι] [DecidableEq ι] in
lemma homogeneous_tubeBaseMatrix_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : Module.Basis ι ℝ S) :
    tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      c • tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  ext i j
  have hh := homogeneous_fiber_hessian_scale hD hs hK hne hc hH hHc (b i,0) (b j,0)
  simp only [normalScale_apply,smul_zero] at hh
  simp only [tubeBaseMatrix,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,hh,mul_neg]

omit [DecidableEq ι] in
lemma homogeneous_tubeFullRadiusMatrix_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : OrthonormalBasis ι ℝ E) :
    tubeFullRadiusMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      c⁻¹ • tubeFullRadiusMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  ext i j
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have hh := homogeneous_fiber_hessian_scale hD hs hK hne hc hH hHc (0,b i) (0,b j)
  have hscale (v : E) : normalScale c ((0:S),v) = c • ((0:S),v) := by simp
  rw [hscale,hscale] at hh
  change fderiv ℝ (fderiv ℝ H) (s,c • e) (c • ((0:S),b i)) (c • ((0:S),b j)) =
    c * fderiv ℝ (fderiv ℝ H) (s,e) (0,b i) (0,b j) at hh
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  change fderiv ℝ (fderiv ℝ H) (s,c • e) (0,b i) (0,b j) =
    c⁻¹ * fderiv ℝ (fderiv ℝ H) (s,e) (0,b i) (0,b j)
  apply (mul_left_cancel₀ hc.ne')
  rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  apply (mul_left_cancel₀ hc.ne')
  exact hh

lemma homogeneous_tubeAngularDensity_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      (c⁻¹)^Fintype.card κ *
        tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  simp only [tubeAngularDensity,homogeneous_tubeFullRadiusMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.adjugate_smul,Matrix.trace_smul,smul_eq_mul,Fintype.card_sum,Fintype.card_unit,
    Nat.add_sub_cancel]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeInvariantSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeFullRadiusMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y i j => tubeFullRadiusMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    (hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const))

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeBaseMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : Module.Basis ι ℝ S) :
    ContDiffAt ℝ ∞ (fun y i j => tubeBaseMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    ((hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const).neg))

omit [CompleteSpace E] in
lemma contDiffAt_tubeAngularDensity {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y => tubeAngularDensity H y b) q := by
  change ContDiffAt ℝ ∞ (fun y => ∑ i, (tubeFullRadiusMatrix H y b).adjugate i i) q
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_adjugate_entries (contDiffAt_tubeFullRadiusMatrix hH b) i i

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualInvariantTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineEpigraph_support_radial {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0) (v : E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hh := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  change ContDiffAt ℝ ∞ H (s,e) at hh
  change fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0
  rw [← second_fderiv_prod_right hh]
  exact homogeneousSupport_hessian_radial (hK s hs) ⟨0,interior_subset (hzero s hs)⟩
    (hh.comp e (contDiffAt_const.prodMk contDiffAt_id)) v

/- The invariant angular determinant is strictly positive on every actual
nonzero fiber conormal, independently of the fixed orthonormal frame. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProjectiveDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma projective_area_exponents (k l : ℕ) {c b q : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    Real.rpow (c^k*b) (1/((k:ℝ)+l+2)) *
      Real.rpow (Real.rpow c (-((l:ℝ)+2))*q) (1-1/((k:ℝ)+l+2)) =
        Real.rpow c (-((l:ℝ)+1)) *
          (Real.rpow b (1/((k:ℝ)+l+2))*Real.rpow q (1-1/((k:ℝ)+l+2))) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hc.le _) hb,
    Real.mul_rpow (Real.rpow_nonneg hc.le _) hq,← Real.rpow_natCast c k,
    ← Real.rpow_mul hc.le,← Real.rpow_mul hc.le]
  rw [show (c^((k:ℝ)*(1/((k:ℝ)+l+2)))*b^(1/((k:ℝ)+l+2))) *
      (c^((-((l:ℝ)+2))*(1-1/((k:ℝ)+l+2)))*q^(1-1/((k:ℝ)+l+2))) =
      (c^((k:ℝ)*(1/((k:ℝ)+l+2))) * c^((-((l:ℝ)+2))*(1-1/((k:ℝ)+l+2)))) *
        (b^(1/((k:ℝ)+l+2))*q^(1-1/((k:ℝ)+l+2))) by ring]
  rw [← Real.rpow_add hc]
  congr 2
  have hd : (k:ℝ)+l+2 ≠ 0 := by positivity
  field_simp
  ring

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- Exact projective-normal normalization of the affine area density. The
factor is c^(-m), where m is the transverse dimension, including m=1.
This is the density factor needed to pass from flat to spherical charts. -/
lemma homogeneous_projective_area_density {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c) (he : ‖e‖ = 1)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hflat : inner ℝ (c • e) (bE (Sum.inr ())) = 1)
    (hrad : ∀ v : E, fderiv ℝ (fderiv ℝ
      (fun q : S × E => homogeneousSupport (K q.1) q.2)) (s,c • e) (0,v) (0,c • e) = 0)
    (hB : 0 ≤ (tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) bS).det)
    (hQ : 0 ≤ tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) bE) :
    let H := fun q : S × E => homogeneousSupport (K q.1) q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) δ =
      Real.rpow c (-((Fintype.card κ:ℝ)+1)) *
        (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
          Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) := by
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have hn : inner ℝ (c • e) (c • e) = c^2 := by
    rw [real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,he]
    ring
  have hq := tubeAngularDensity_flat hHc bE hflat hrad
  rw [homogeneous_tubeAngularDensity_scale hD hs hK hne hc hH hHc,hn] at hq
  change (c⁻¹)^Fintype.card κ * tubeAngularDensity H (s,e) bE =
    (tubeRadiusMatrix H (s,c • e) bE).det * c^2 at hq
  have hr : (tubeRadiusMatrix H (s,c • e) bE).det =
      Real.rpow c (-((Fintype.card κ:ℝ)+2)) * tubeAngularDensity H (s,e) bE := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hc.le,Real.rpow_add hc,Real.rpow_natCast,Real.rpow_two]
    rw [inv_pow] at hq
    apply (mul_left_injective₀ (show c^Fintype.card κ*c^2 ≠ 0 by positivity))
    field_simp [hc.ne'] at hq ⊢
    nlinarith [hq]
  change tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) _ = _
  rw [tubeAreaDensity,homogeneous_tubeBaseMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.det_smul,hr]
  exact projective_area_exponents _ _ hc hB hQ

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualProjectiveDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ActualProjectiveDensity
open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- Exact flat/spherical density normalization for the genuine epigraph support.
There are no assumed homogeneity or radial-Hessian identities here. -/
theorem affineEpigraph_projective_area_density {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : ‖e‖ = 1)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {c : ℝ} (hc : 0 < c) (hflat : inner ℝ (c • e) (bE (Sum.inr ())) = 1) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) δ =
      Real.rpow c (-((Fintype.card κ:ℝ)+1)) *
        (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
          Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) := by
  have he0 : e ≠ 0 := by intro heq; simp [heq] at he
  have hce : c • e ≠ 0 := smul_ne_zero hc.ne' he0
  have hp' := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he0 bS bE
  exact homogeneous_projective_area_density hD hs hK
    (fun s hs => ⟨0,interior_subset (hzero s hs)⟩) hc he
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he0).1
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs hce).1 bS bE hflat
    (fun v => affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hs hce v)
    hp'.1.det_pos.le hp'.2.1.le

end ActualProjectiveDensity

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProjectiveWeightContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open intervalIntegral

lemma lintegral_smul_jacobian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (f : F → ℝ≥0∞)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t^Module.finrank ℝ F) * (∫⁻ x, f (t • x) ∂μ) = ∫⁻ x, f x ∂μ := by
  have hm := lintegral_map_equiv (μ := μ) f
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr ht.ne').unit).toMeasurableEquiv
  change (∫⁻ x, f x ∂Measure.map (fun x : F => t • x) μ) = ∫⁻ x, f (t • x) ∂μ at hm
  rw [Measure.map_addHaar_smul μ ht.ne',lintegral_smul_measure] at hm
  rw [← hm,smul_eq_mul,← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg ht.le _)]
  rw [abs_of_pos (inv_pos.mpr (pow_pos ht _)),mul_inv_cancel₀ (pow_pos ht _).ne']
  simp

lemma projective_norm_pos {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : F) : 0 < ‖WithLp.toLp 2 (x,(1:ℝ))‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hh := congrArg (fun q : WithLp 2 (F × ℝ) => (WithLp.ofLp q).2) h
  simp at hh

/- Exact radial slice integral, retaining the dimension-zero tangent endpoint. -/
lemma lintegral_pow_Ioo {k : ℕ} {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ioo 0 r, ENNReal.ofReal (t^k)) = ENNReal.ofReal (r^(k+1)/(k+1)) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow k).1]
  · rw [← intervalIntegral.integral_of_le hr.le]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg ht.1.le _

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualProjectiveAreaChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ActualProjectiveAreaChart
open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A true affine area density in any isometric projective chart;
the spherical angular basis can be chosen independently of the planar one. -/
theorem affineEpigraph_projective_isometry_area_density {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) (bS : Module.Basis ι ℝ S)
    (bE bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E)
    (hlast : bE (Sum.inr ()) = f (WithLp.toLp 2 (0,(1:ℝ)))) (x : F) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    let p := f (WithLp.toLp 2 (x,(1:ℝ)))
    let e := f (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ)))
    ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (s,p) bS) (tubeRadiusMatrix H (s,p) bE) δ) =
      ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^ (Module.finrank ℝ F+1)) *
      ENNReal.ofReal (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
        Real.rpow (tubeAngularDensity H (s,e) bRef) (1-δ)) := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
  let p₀ := WithLp.toLp 2 (x,(1:ℝ))
  let c := ‖p₀‖
  let p := f p₀
  let e := f (c⁻¹ • p₀)
  have hc : 0 < c := projective_norm_pos x
  have he : ‖e‖ = 1 := by
    simp only [e,f.norm_map,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    exact inv_mul_cancel₀ hc.ne'
  have hce : c • e = p := by simp [e,p,map_smul,smul_smul,hc.ne']
  have hf : inner ℝ (c • e) (bE (Sum.inr ())) = 1 := by
    rw [hce,hlast]
    change inner ℝ (f p₀) (f (WithLp.toLp 2 (0,(1:ℝ)))) = 1
    rw [f.inner_map_map]
    change inner ℝ x (0:F) + inner ℝ (1:ℝ) 1 = 1
    simp
  have hh := affineEpigraph_projective_area_density hΩ hcv hu hp a L hD hK hzero
    hs he bS bE hc hf
  change tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) δ =
    Real.rpow c (-((Fintype.card κ:ℝ)+1)) *
      (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
        Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) at hh
  rw [hce, tubeAngularDensity_basis_independent H (s,e) bRef bE] at hh
  have hcard : Fintype.card κ = Module.finrank ℝ F := by
    have hc := (Module.finrank_eq_card_basis bE.toBasis).symm
    have hd : Module.finrank ℝ E = Module.finrank ℝ F + 1 := by
      rw [← f.toLinearEquiv.finrank_eq,(WithLp.linearEquiv 2 ℝ (F × ℝ)).finrank_eq,
        Module.finrank_prod,Module.finrank_self]
    simp only [Fintype.card_sum,Fintype.card_unit] at hc
    change Fintype.card κ + 1 = Module.finrank ℝ E at hc
    omega
  have hexp : Real.rpow c (-((Fintype.card κ:ℝ)+1)) = c⁻¹^(Module.finrank ℝ F+1) := by
    simp only [Real.rpow_eq_pow]
    rw [show -((Fintype.card κ:ℝ)+1) = -((Fintype.card κ+1:ℕ):ℝ) by norm_num,
      Real.rpow_neg hc.le,Real.rpow_natCast,inv_pow,hcard]
  dsimp only
  change ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (s,p) bS)
    (tubeRadiusMatrix H (s,p) bE) δ) = _
  rw [hh,hexp,ENNReal.ofReal_mul (by positivity)]

end ActualProjectiveAreaChart


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GaussSurjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GaussSurjectivity
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The gradient of a convex defining function at a zero level point is an
outward supporting covector, and cannot vanish when a strict sublevel point exists. -/
lemma convex_sublevel_gradient_support {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {y z : E} (hy : y ∈ W) (hz : z ∈ W)
    (hyF : F y = 0) (hzF : F z < 0) (hd : DifferentiableAt ℝ F y) :
    gradient F y ≠ 0 ∧ IsMaxOn (fun x => inner ℝ (gradient F y) x)
      {x | x ∈ W ∧ F x ≤ 0} y := by
  have hgrad (x : E) : inner ℝ (gradient F y) x = fderiv ℝ F y x := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  constructor
  · intro he
    have hh := convex_first_order hcv hy hz hd
    have hz' := hgrad (z-y)
    rw [he,inner_zero_left] at hz'
    rw [← hz',hyF] at hh
    linarith
  · intro x hx
    have hh := convex_first_order hcv hy hx.1 hd
    rw [← hgrad,inner_sub_right,hyF] at hh
    change inner ℝ (gradient F y) x ≤ inner ℝ (gradient F y) y
    linarith [hx.2]

end GaussSurjectivity


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineGaussSurjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section AffineGaussSurjectivity
open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The full boundary above the regular base domain is covered by actual
support gradients, including the direction obtained from the original graph. -/
theorem affineEpigraph_gauss_surjective {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {y : E} (hy : (a+L (s,y)).1 ∈ Ω)
    (hyF : affineDefining u a L (s,y) = 0) :
    let e := gradient (fun q => affineDefining u a L (s,q)) y
    e ≠ 0 ∧ ∀ c : ℝ, 0 < c →
      gaussPoint {q | (s,q) ∈ affineEpigraphPullback Ω u a L} (c • e) = y := by
  let W : Set (S × E) := {p | (a + L p).1 ∈ Ω}
  let F : S × E → ℝ := fun p => u (a + L p).1 - (a + L p).2
  have hbase : ContDiff ℝ ∞ (fun p : S × E => (a + L p).1) :=
    (contDiff_const.add L.contDiff).fst
  have hheight : ContDiff ℝ ∞ (fun p : S × E => (a + L p).2) :=
    (contDiff_const.add L.contDiff).snd
  have hW : IsOpen W := hΩ.preimage hbase.continuous
  have hF : ContDiffOn ℝ ∞ F W :=
    (hu.comp hbase.contDiffOn (fun _ h => h)).sub hheight.contDiffOn
  have hFu : ConvexOn ℝ Ω u :=
    convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hFeq (r : S) : (fun q => F (r, q)) = (fun q =>
      u ((a + L (r, 0)).1 + affineFiberHorizontal L q) -
        ((a + L (r, 0)).2 + affineFiberHeight L q)) := by
    funext q
    change u (a + L (r, q)).1 - (a + L (r, q)).2 = _
    rw [affine_coordinates_split a L r q]
  have hWeq (r : S) : {y | (r, y) ∈ W} =
      {y | (a + L (r, 0)).1 + affineFiberHorizontal L y ∈ Ω} := by
    ext y
    change (a + L (r, y)).1 ∈ Ω ↔ _
    rw [affine_coordinates_split a L r y]
    rfl
  have hcvF (r : S) : ConvexOn ℝ {y | (r, y) ∈ W} (fun y => F (r, y)) := by
    rw [hFeq, hWeq]
    exact convexOn_affineSlice hFu (a + L (r, 0)).1 (a + L (r, 0)).2
      (affineFiberHorizontal L) (affineFiberHeight L)
  have hKeq (r : S) : {y | (r, y) ∈ W ∧ F (r, y) ≤ 0} =
      {y | (r, y) ∈ affineEpigraphPullback Ω u a L} := by
    ext y
    simp only [W, F, affineEpigraphPullback, mem_ofPred_eq, sub_nonpos]
  have hK' : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by rw [hKeq]; exact hK s hs
  have hzero' : (0 : E) ∈ interior {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by
    rw [hKeq]; exact hzero s hs
  have hA : Function.Injective (affineFiberHorizontal L) :=
    affineFiberHorizontal_injective (hK s hs) ⟨0, interior_subset (hzero s hs)⟩
  have hH (y : E) (hy : (s, y) ∈ W) (v : E) (hv : v ≠ 0) :
      0 < fderiv ℝ (fderiv ℝ (fun q => F (s, q))) y v v := by
    have huc := hu.contDiffAt (hΩ.mem_nhds hy)
    have hx : (a + L (s, y)).1 = (a + L (s, 0)).1 + affineFiberHorizontal L y :=
      congrArg Prod.fst (affine_coordinates_split a L s y)
    rw [hFeq, affineSlice_second (by rw [← hx]; exact huc)]
    exact second_fderiv_pos (by rw [← hx]; exact huc)
      (by rw [← hx]; exact hp _ hy)
      (fun hh => hv (hA (by simpa using hh)))
  have hzW : (s, (0 : E)) ∈ W := (interior_subset hzero').1
  have hzF : F (s, 0) < 0 := sublevel_interior_strict (hcvF s) hzero'
    (((hF.contDiffAt (hW.mem_nhds hzW)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) (hH 0 hzW)

  have hdy : DifferentiableAt ℝ (fun q => F (s,q)) y :=
    (((hF.contDiffAt (hW.mem_nhds hy)).comp y
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
  have hgy := convex_sublevel_gradient_support (hcvF s) hy hzW hyF hzF hdy
  dsimp only
  refine ⟨hgy.1, ?_⟩
  intro c hc
  let e := gradient (fun q => F (s,q)) y
  have hce : c • e ≠ 0 := smul_ne_zero hc.ne' hgy.1
  have hm : IsMaxOn (fun q => inner ℝ (c • e) q)
      {q | (s,q) ∈ affineEpigraphPullback Ω u a L} y := by
    intro q hq
    change inner ℝ (c • e) q ≤ inner ℝ (c • e) y
    simp only [inner_smul_left,conj_trivial]
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply hgy.2
    change q ∈ {q | (s,q) ∈ W ∧ F (s,q) ≤ 0}
    rwa [hKeq]
  have hyv : y ∈ {q | (s,q) ∈ affineEpigraphPullback Ω u a L} := by
    rw [← hKeq]
    exact ⟨hy,hyF.le⟩
  have hj := (affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero hs hce).1
  exact gaussPoint_eq_of_max (hK s hs) hyv (homogeneousSupport_eq_of_max hyv hm)
    ((hj.comp (c • e) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))

end AffineGaussSurjectivity

-- WholeSphereArea

end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FiniteProjectiveCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {τ : Type*} [Fintype τ]

lemma projectiveAxis_norm (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) :
    ‖projectiveAxis f‖ = 1 := by
  simp [projectiveAxis]

lemma projectiveAxis_inner (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (v : E) :
    inner ℝ v (projectiveAxis f) = (WithLp.ofLp (f.symm v)).2 := by
  rw [← f.apply_symm_apply v]
  change inner ℝ (f (f.symm v)) (f (WithLp.toLp 2 (0,(1:ℝ)))) = _
  rw [f.inner_map_map]
  simp [WithLp.prod_inner_apply]

lemma projectiveFrameAt_axis (b : OrthonormalBasis τ ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (j : τ) :
    projectiveAxis (projectiveFrameAt b f j) = b j := by
  apply Submodule.reflection_sub
  rw [projectiveAxis_norm,b.norm_eq_one]

/-- A concrete finite full covering by positive projective hemispheres;
there is no discarded equator in this pointwise statement. -/
lemma signedProjectiveFrame_cover (b : OrthonormalBasis τ ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) {v : E} (hv : v ≠ 0) :
    ∃ j : τ × Bool, 0 < inner ℝ v (projectiveAxis (signedProjectiveFrame b f j)) := by
  have hex : ∃ j : τ, inner ℝ v (b j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply b.repr.injective
    ext j
    simp only [map_zero,PiLp.zero_apply,OrthonormalBasis.repr_apply_apply]
    simpa only [real_inner_comm] using h j
  obtain ⟨j,hj⟩ := hex
  rcases lt_or_gt_of_ne hj with hn | hp
  · refine ⟨(j,false),?_⟩
    change 0 < inner ℝ v (-projectiveAxis (projectiveFrameAt b f j))
    rw [inner_neg_right,projectiveFrameAt_axis]
    linarith
  · refine ⟨(j,true),?_⟩
    change 0 < inner ℝ v (projectiveAxis (projectiveFrameAt b f j))
    rwa [projectiveFrameAt_axis]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatGraphCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section FlatGraphCoverage
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma flatGraphChart_covers_direction {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ)
    (φ : OpenPartialHomeomorph (Space n) (Space n)) {D Q : Set S}
    (hsource : φ.source = {x | (flatProductCoordinates bS bF e x).1 ∈ D})
    (heφ : ∀ x ∈ φ.source, a+L ((flatProductCoordinates bS bF e x).1,
      gaussPoint {y | ((flatProductCoordinates bS bF e x).1,y) ∈ affineEpigraphPullback Ω u a L}
        (f (WithLp.toLp 2 ((flatProductCoordinates bS bF e x).2,(1:ℝ))))) = (φ x,u (φ x)))
    (hQD : Q ⊆ D) {s : S} (hs : s ∈ Q) {y v : E}
    (hgauss : ∀ c : ℝ, 0 < c → gaussPoint {q | (s,q) ∈ affineEpigraphPullback Ω u a L} (c • v) = y)
    (hdir : 0 < inner ℝ v (projectiveAxis f)) :
    (a+L (s,y)).1 ∈ φ '' ((flatProductCoordinates bS bF e) ⁻¹' (Q ×ˢ Set.univ)) := by
  let Z := flatProductCoordinates bS bF e
  let c := (inner ℝ v (projectiveAxis f))⁻¹
  have hc : 0 < c := inv_pos.mpr hdir
  let p := f.symm (c • v)
  have hp : (WithLp.ofLp p).2 = 1 := by
    rw [← projectiveAxis_inner f (c • v)]
    simp only [inner_smul_left,conj_trivial]
    exact inv_mul_cancel₀ hdir.ne'
  let x := Z.symm (s,(WithLp.ofLp p).1)
  have hx : Z x = (s,(WithLp.ofLp p).1) := Z.apply_symm_apply _
  have hxQ : x ∈ Z ⁻¹' (Q ×ˢ univ) := by simp only [mem_preimage,hx,mem_prod,mem_univ,and_true]; exact hs
  have hxs : x ∈ φ.source := by rw [hsource]; change (Z x).1 ∈ D; rw [hx]; exact hQD hs
  have hflat : f (WithLp.toLp 2 ((WithLp.ofLp p).1,(1:ℝ))) = c • v := by
    rw [← hp]
    change f p = c • v
    exact f.apply_symm_apply _
  refine ⟨x,hxQ,?_⟩
  have h := heφ x hxs
  change a+L ((Z x).1,gaussPoint _ (f (WithLp.toLp 2 ((Z x).2,(1:ℝ))))) = _ at h
  rw [hx,hflat,hgauss c hc] at h
  exact (congrArg Prod.fst h).symm

end FlatGraphCoverage

-- WholeGraphAreaTransport

end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphereIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma linearIsometrySphere_cone_preimage (f : E ≃ₗᵢ[ℝ] F)
    (s : Set (Metric.sphere (0:F) 1)) :
    f ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0:ℝ) 1 • (Subtype.val '' ((linearIsometrySphereHomeomorph f) ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨t,ht,y,⟨e,he,rfl⟩,h⟩
    let d : Metric.sphere (0:E) 1 := ⟨f.symm e,by
      simp⟩
    refine ⟨t,ht,d,⟨d,?_,rfl⟩,?_⟩
    · change linearIsometrySphereHomeomorph f d ∈ s
      have hd : linearIsometrySphereHomeomorph f d = e := by ext; simp [d]
      rwa [hd]
    · apply f.injective
      simpa [d] using h
  · rintro ⟨t,ht,y,⟨e,he,rfl⟩,h⟩
    refine ⟨t,ht,f e,⟨linearIsometrySphereHomeomorph f e,he,rfl⟩,?_⟩
    rw [← h,map_smul]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/- The Haar-induced sphere measure is preserved by every linear isometry.
No surface-measure normalization or Jacobian identity is assumed. -/
theorem linearIsometrySphere_measurePreserving (f : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (linearIsometrySphereHomeomorph f)
      (volume : Measure E).toSphere (volume : Measure F).toSphere := by
  refine ⟨(linearIsometrySphereHomeomorph f).measurable,?_⟩
  ext s hs
  rw [Measure.map_apply (linearIsometrySphereHomeomorph f).measurable hs,
    Measure.toSphere_apply' _ ((linearIsometrySphereHomeomorph f).measurable hs),
    Measure.toSphere_apply' _ hs,← linearIsometrySphere_cone_preimage]
  have hp (t : Set F) : volume (f ⁻¹' t) = volume t := by
    calc
      volume (f ⁻¹' t) = (Measure.map f volume) t :=
        (f.toHomeomorph.measurableEmbedding.map_apply volume t).symm
      _ = volume t := congrArg (fun μ : Measure F => μ t) f.measurePreserving.map_eq
  rw [hp,f.toLinearEquiv.finrank_eq]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProductEquator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma product_vertical_hyperplane_volume_zero :
    volume {x : WithLp 2 (F × ℝ) | (WithLp.ofLp x).2 = 0} = 0 := by
  have he : {x : WithLp 2 (F × ℝ) | (WithLp.ofLp x).2 = 0} =
      WithLp.ofLp ⁻¹' ((univ : Set F) ×ˢ ({0} : Set ℝ)) := by ext x; simp
  rw [he,(WithLp.volume_preserving_ofLp F ℝ).measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet]
  change ((volume : Measure F).prod (volume : Measure ℝ)) (univ ×ˢ {0}) = 0
  rw [Measure.prod_prod,measure_singleton,mul_zero]

/- The equator is null for the actual Haar-induced sphere measure. -/
lemma product_sphere_equator_null :
    (volume : Measure (WithLp 2 (F × ℝ))).toSphere
      {e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 | (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 = 0} = 0 := by
  have hs : MeasurableSet {e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 |
      (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 = 0} := by
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [Measure.toSphere_apply' _ hs]
  have hh : volume (Ioo (0:ℝ) 1 • (Subtype.val ''
      {e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 |
        (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 = 0})) = 0 := by
    apply measure_mono_null _ product_vertical_hyperplane_volume_zero
    rintro x ⟨t,ht,y,⟨e,he,rfl⟩,rfl⟩
    simpa using congrArg (fun a : ℝ => t*a) he
  rw [hh,mul_zero]

/- Full-sphere nonnegative integration is the sum of the two open hemispheres.
The codimension-one null set is proved from product volume, including dim F=0. -/
theorem product_sphere_lintegral_split (g : WithLp 2 (F × ℝ) → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1, g e ∂volume.toSphere) =
      (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
        if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g e else 0 ∂volume.toSphere) +
      (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
        if (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 < 0 then g e else 0 ∂volume.toSphere) := by
  have hne : ∀ᵐ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 ∂volume.toSphere,
      (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 ≠ 0 := by
    rw [ae_iff]
    simpa using (product_sphere_equator_null (F:=F))
  have hf : Measurable (fun e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 =>
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g e else 0) := by
    exact (hg.comp measurable_subtype_coe).ite
      ((isOpen_lt continuous_const (by fun_prop)).measurableSet) measurable_const
  rw [← lintegral_add_left hf]
  apply lintegral_congr_ae
  filter_upwards [hne] with e he
  rcases lt_or_gt_of_ne he with h | h
  · simp only [ite_eq_left h,ite_eq_right (not_lt_of_ge h.le),zero_add]
  · simp only [ite_eq_left h,ite_eq_right (not_lt_of_ge h.le),add_zero]

/- Antipodal transport identifies the negative hemisphere with a positive one. -/
theorem product_sphere_negative_lintegral (g : WithLp 2 (F × ℝ) → ℝ≥0∞) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 < 0 then g e else 0 ∂volume.toSphere) =
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g (- (e:WithLp 2 (F × ℝ)))
      else 0 ∂volume.toSphere) := by
  have h := (linearIsometrySphere_measurePreserving
    (LinearIsometryEquiv.neg ℝ (E:=WithLp 2 (F × ℝ)))).lintegral_comp_emb
      (linearIsometrySphereHomeomorph
        (LinearIsometryEquiv.neg ℝ (E:=WithLp 2 (F × ℝ)))).measurableEmbedding
      (fun e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1 =>
        if (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 < 0 then g e else 0)
  symm
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro e
  simp
  rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProjectiveCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral

section ProjectiveCone
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/- Ordinary-volume computation of a projective cone. Together with polar
coordinates this yields the hemisphere chart density without assuming a
surface-area formula. -/
theorem projective_cone_lintegral (f : WithLp 2 (F × ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : WithLp 2 (F × ℝ)) (t : ℝ), 0 < t → f (t • x) = f x) :
    (∫⁻ t in Ioi (0:ℝ), ∫⁻ x : F,
      if ‖WithLp.toLp 2 (x,t)‖ < 1 then f (WithLp.toLp 2 (x,t)) else 0) =
        ∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
          (Module.finrank ℝ F+1) / (Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ))) := by
  let k := Module.finrank ℝ F
  let p := fun x : F => WithLp.toLp 2 (x,(1:ℝ))
  let G : F × ℝ → ℝ≥0∞ := fun q =>
    if ‖WithLp.toLp 2 q‖ < 1 then f (WithLp.toLp 2 q) else 0
  have hG : Measurable G := by
    apply Measurable.ite
    · exact measurableSet_lt (by fun_prop) measurable_const
    · exact hf.comp (MeasurableEquiv.toLp 2 (F × ℝ)).measurable
    · exact measurable_const
  let H : ℝ → F → ℝ≥0∞ := fun t x =>
    if t < ‖p x‖⁻¹ then ENNReal.ofReal (t^k)*f (p x) else 0
  have hH : Measurable (Function.uncurry H) := by
    apply Measurable.ite
    · apply measurableSet_lt measurable_fst
      dsimp [p]
      fun_prop
    · exact (by fun_prop : Measurable (fun q : ℝ × F => ENNReal.ofReal (q.1^k))).mul
        (hf.comp (by dsimp [p]; fun_prop))
    · exact measurable_const
  have hs (t : ℝ) (ht : 0 < t) : (∫⁻ x : F, G (x,t)) = ∫⁻ x : F, H t x := by
    rw [← lintegral_smul_jacobian volume (fun x : F => G (x,t)) ht]
    rw [← lintegral_const_mul _ (show Measurable (fun x : F => G (t • x,t)) from
      hG.comp (by fun_prop))]
    apply lintegral_congr
    intro x
    have he : WithLp.toLp 2 (t • x,t) = t • p x := by
      rw [← WithLp.toLp_smul]
      congr 1
      simp [Prod.smul_mk]
    dsimp only [G,H]
    rw [he,hscale _ t ht,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hn : 0 < ‖p x‖ := projective_norm_pos x
    simp only [← one_div ‖p x‖,lt_div_iff₀ hn]
    split_ifs <;> simp [k]
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ x : F, H t x := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hs t ht
    _ = ∫⁻ x : F, ∫⁻ t in Ioi (0:ℝ), H t x :=
      lintegral_lintegral_swap hH.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      have hn : 0 < ‖p x‖⁻¹ := inv_pos.mpr (projective_norm_pos x)
      change (∫⁻ t in Ioi (0:ℝ), (Iio ‖p x‖⁻¹).indicator
        (fun t => ENNReal.ofReal (t^k)*f (p x)) t) = _
      rw [lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
      have he : Iio ‖p x‖⁻¹ ∩ Ioi (0:ℝ) = Ioo 0 ‖p x‖⁻¹ := by ext t; simp [and_comm]
      rw [he,lintegral_mul_const _ (by fun_prop),lintegral_pow_Ioo hn]

end ProjectiveCone

/- A homogeneous quantity which expands on inward rays has its spherical
integral controlled by its integral over the punctured unit ball. The exact
radial Haar normalization is retained. -/
lemma sphere_lintegral_mul_radial_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞}
    (hf : Measurable (fun e : Metric.sphere (0:E) 1 => f e))
    (hscale : ∀ (e : Metric.sphere (0:E) 1) (r : ℝ), 0 < r → r < 1 → f e = f (r • (e:E))) :
    (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) *
      ENNReal.ofReal (1 / ((Module.finrank ℝ E - 1 + 1 : ℕ):ℝ)) =
        ∫⁻ x in Metric.ball (0:E) 1 \ {0}, f x ∂μ := by
  let Φ := homeomorphUnitSphereProd E
  let ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let r₁ : Ioi (0:ℝ) := ⟨1,by change (0:ℝ) < 1; exact one_pos⟩
  let U : Set (Metric.sphere (0:E) 1 × Ioi (0:ℝ)) := univ ×ˢ Iio r₁
  have hU : MeasurableSet U := MeasurableSet.univ.prod measurableSet_Iio
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hprod : (∫⁻ q in U, f q.1 ∂μ.toSphere.prod ν) =
      (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) *
        ENNReal.ofReal (1 / ((Module.finrank ℝ E - 1 + 1 : ℕ):ℝ)) := by
    dsimp only [U]
    rw [setLIntegral_prod (fun q : Metric.sphere (0:E) 1 × Ioi (0:ℝ) => f q.1)
      ((hf.comp measurable_fst).aemeasurable)]
    simp only [lintegral_const,Measure.restrict_apply_univ,Measure.restrict_univ]
    rw [lintegral_mul_const _ hf]
    simp [ν,r₁,Measure.volumeIoiPow_apply_Iio]
  have hsub : Subtype.val '' (Φ ⁻¹' U) = Metric.ball (0:E) 1 \ {0} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,z.property⟩
      rw [Metric.mem_ball,dist_zero_right]
      have hz2 : ((Φ z).2:ℝ) < 1 := hz.2
      simpa [Φ,homeomorphUnitSphereProd_apply_snd_coe] using hz2
    · intro hx
      refine ⟨⟨x,hx.2⟩,?_,rfl⟩
      change True ∧ ((Φ ⟨x,hx.2⟩).2:ℝ) < 1
      exact ⟨trivial,by simpa [Φ,homeomorphUnitSphereProd_apply_snd_coe,
        Metric.mem_ball,dist_zero_right] using hx.1⟩
  have heq : (∫⁻ q in U, f ((Φ.symm q):E) ∂μ.toSphere.prod ν) =
      ∫⁻ x in Metric.ball (0:E) 1 \ {0}, f x ∂μ := by
    rw [← hmp.setLIntegral_comp_preimage_emb Φ.measurableEmbedding
      (fun q => f ((Φ.symm q):E)) U]
    simp only [Φ,Homeomorph.symm_apply_apply]
    rw [setLIntegral_subtype (measurableSet_singleton (0:E)).compl,hsub]
  rw [← hprod,← heq]
  apply setLIntegral_congr_fun hU
  intro q hq
  have hr : (q.2:ℝ) < 1 := hq.2
  simpa only [Φ,homeomorphUnitSphereProd_symm_apply_coe] using hscale q.1 q.2 q.2.property hr

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProjectiveHemisphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma projective_cone_lintegral_eq_global
    (f : WithLp 2 (F × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in Metric.ball (0:WithLp 2 (F × ℝ)) 1 \ {0},
      if 0 < (WithLp.ofLp y).2 then f y else 0) =
    ∫⁻ t in Ioi (0:ℝ), ∫⁻ x : F,
      if ‖WithLp.toLp 2 (x,t)‖ < 1 then f (WithLp.toLp 2 (x,t)) else 0 := by
  let A := Metric.ball (0:WithLp 2 (F × ℝ)) 1 \ {0}
  let g : WithLp 2 (F × ℝ) → ℝ≥0∞ := fun y => if 0 < (WithLp.ofLp y).2 then f y else 0
  let G : F × ℝ → ℝ≥0∞ := fun q =>
    if 0 < q.2 then (if ‖WithLp.toLp 2 q‖ < 1 then f (WithLp.toLp 2 q) else 0) else 0
  have hG : Measurable G := by
    apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    · apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      · exact hf.comp (MeasurableEquiv.toLp 2 (F × ℝ)).measurable
      · exact measurable_const
    · exact measurable_const
  have he (q : F × ℝ) : A.indicator g (WithLp.toLp 2 q) = G q := by
    by_cases ht : 0 < q.2
    · have hq : WithLp.toLp 2 q ≠ 0 := by
        intro h
        have hh := congrArg (fun y : WithLp 2 (F × ℝ) => (WithLp.ofLp y).2) h
        have hq2 : q.2 = 0 := hh
        exact ht.ne' hq2
      simp [A,g,G,Set.indicator,Metric.mem_ball,dist_zero_right,ht,hq]
    · simp [A,g,G,Set.indicator,ht]
  change (∫⁻ y in A, g y) = _
  rw [← lintegral_indicator (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton _))]
  rw [← (WithLp.volume_preserving_toLp F ℝ).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (F × ℝ)).measurableEmbedding (A.indicator g)]
  simp_rw [he]
  rw [MeasureTheory.Measure.volume_eq_prod,lintegral_prod_symm G hG.aemeasurable]
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  by_cases ht : 0 < t
  · simp [G,Set.indicator,ht]
  · simp [G,Set.indicator,ht]

/- Exact projective-coordinate formula for the genuine Euclidean hemisphere
measure. This is proved from Haar polar coordinates and ordinary-volume
scaling, not an assumed surface-area/Jacobian identity. The tangent space may
have dimension zero. -/
theorem projective_hemisphere_lintegral
    (f : WithLp 2 (F × ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : WithLp 2 (F × ℝ)) (t : ℝ), 0 < t → f (t • x) = f x) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then f e else 0 ∂volume.toSphere) =
    ∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ))) := by
  let E := WithLp 2 (F × ℝ)
  let g : E → ℝ≥0∞ := fun y => if 0 < (WithLp.ofLp y).2 then f y else 0
  have hg : Measurable g := by
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) hf measurable_const
  have hgs (y : E) (t : ℝ) (ht : 0 < t) : g (t • y) = g y := by
    have hm : (WithLp.ofLp (t • y)).2 = t * (WithLp.ofLp y).2 := rfl
    dsimp only [g]
    simp only [hm,hscale y t ht,mul_pos_iff_of_pos_left ht]
  have hh := sphere_lintegral_mul_radial_eq (volume : Measure E)
    (hg.comp measurable_subtype_coe) (fun e r hr _ => (hgs e r hr).symm)
  have hd : Module.finrank ℝ E = Module.finrank ℝ F + 1 := by
    change Module.finrank ℝ (WithLp 2 (F × ℝ)) = _
    rw [(WithLp.linearEquiv 2 ℝ (F × ℝ)).finrank_eq,Module.finrank_prod,Module.finrank_self]
  rw [hd,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hh
  rw [projective_cone_lintegral_eq_global f hf,projective_cone_lintegral f hf hscale] at hh
  let c : ℝ≥0∞ := ENNReal.ofReal (1/((Module.finrank ℝ F:ℝ)+1))
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hp : Measurable (fun x : F => ENNReal.ofReal
      (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^ (Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ)))) := by
    apply Measurable.mul
    · fun_prop
    · exact hf.comp (by fun_prop)
  have he (x : F) : ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)/(Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ))) =
      (ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ)))) * c := by
    dsimp [c]
    rw [div_eq_mul_inv,ENNReal.ofReal_mul (by positivity)]
    simp only [one_div]
    ac_rfl
  simp_rw [he] at hh
  rw [lintegral_mul_const _ hp] at hh
  exact (ENNReal.mul_left_inj hc ENNReal.ofReal_ne_top).mp hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProjectiveNormalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/- The projective hemisphere formula for an arbitrary measurable integrand,
with the normalization map written explicitly. -/
theorem projective_hemisphere_normalized_lintegral
    (g : WithLp 2 (F × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g e else 0 ∂volume.toSphere) =
    ∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) *
      g (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ))) := by
  let f : WithLp 2 (F × ℝ) → ℝ≥0∞ := fun y => g (‖y‖⁻¹ • y)
  have hf : Measurable f := hg.comp (by fun_prop)
  have hscale (y : WithLp 2 (F × ℝ)) (t : ℝ) (ht : 0 < t) : f (t • y) = f y := by
    dsimp [f]
    congr 1
    rw [norm_smul,Real.norm_of_nonneg ht.le,mul_inv_rev,smul_smul]
    congr 1
    rw [mul_assoc,inv_mul_cancel₀ ht.ne',mul_one]
  have h := projective_hemisphere_lintegral f hf hscale
  have hs (e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1) : f e = g e := by
    have he : ‖(e:WithLp 2 (F × ℝ))‖ = 1 := by
      exact norm_eq_of_mem_sphere e
    simp [f,he]
  simp_rw [hs] at h
  exact h

/- Substitution of a pointwise density identity into the exact hemisphere
formula. The density law need only hold on this chart, and the tangent space
may be zero-dimensional. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WholeSphereProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

section WholeSphereProjective
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/- Exact two-chart projective integration on the actual sphere. -/
theorem sphere_two_projective_lintegral (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ e : Metric.sphere (0:E) 1, g e ∂volume.toSphere) =
    (∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) *
      g (f (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ))))) +
    (∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) *
      g (-f (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ))))) := by
  rw [← (linearIsometrySphere_measurePreserving f).lintegral_comp_emb
    (linearIsometrySphereHomeomorph f).measurableEmbedding]
  simp only [linearIsometrySphereHomeomorph_coe]
  rw [product_sphere_lintegral_split (fun e => g (f e)) (hg.comp f.continuous.measurable),
    product_sphere_negative_lintegral (fun e => g (f e)),
    projective_hemisphere_normalized_lintegral (fun e => g (f e)) (hg.comp f.continuous.measurable),
    projective_hemisphere_normalized_lintegral (fun e => g (f (-e))) (by fun_prop)]
  simp only [map_neg]

end WholeSphereProjective

open Filter
open scoped Topology

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SphericalAreaContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SphericalAreaContinuity
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [CompleteSpace E] in
lemma continuousAt_sphericalArea {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ)
    (hB : 0 < (tubeBaseMatrix H q bS).det) (hQ : 0 < tubeAngularDensity H q bE) :
    ContinuousAt (fun y => Real.rpow (tubeBaseMatrix H y bS).det δ *
        Real.rpow (tubeAngularDensity H y bE) (1-δ)) q := by
  have hb := (contDiffAt_tubeBaseMatrix hH bS).continuousAt
  have hq := (contDiffAt_tubeAngularDensity hH bE).continuousAt
  have hd := continuous_id.matrix_det.continuousAt.comp hb
  exact (hd.rpow_const (Or.inl hB.ne')).mul (hq.rpow_const (Or.inl hQ.ne'))
end SphericalAreaContinuity

section WholeSphereArea
open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The actual full-sphere affine area is the sum of the two actual flat chart areas.
Both flat charts are complete; their omitted equator has actual sphere measure zero. -/
theorem affineEpigraph_sphere_area_two_flat_lintegral {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) (bS : Module.Basis ι ℝ S)
    (bF : OrthonormalBasis κ ℝ F) (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E)  :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    let flatEnergy := fun h : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E => fun x : F =>
      ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) bS)
        (tubeRadiusMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) (flatProductFiberBasis bF h)) δ)
    (∫⁻ e : Metric.sphere (0:E) 1, ENNReal.ofReal
      (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
        Real.rpow (tubeAngularDensity H (s,e) bRef) (1-δ))
        ∂volume.toSphere) = (∫⁻ x : F, flatEnergy f x) +
      (∫⁻ x : F, flatEnergy (f.trans (LinearIsometryEquiv.neg ℝ)) x) := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
  let g : E → ℝ≥0∞ := fun e => ENNReal.ofReal
    (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
      Real.rpow (tubeAngularDensity H (s,e) bRef) (1-δ))
  have hg : Measurable g := by
    apply ENNReal.measurable_ofReal.comp
    apply measurable_of_continuousOn_compl_singleton (0:E)
    intro e he
    have he0 : e ≠ 0 := by simpa using he
    have hj := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he0).1
    have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he0 bS bRef
    exact ((continuousAt_sphericalArea hj bS bRef δ hpos.1.det_pos hpos.2.1).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  change (∫⁻ e : Metric.sphere (0:E) 1, g e ∂volume.toSphere) = _
  rw [sphere_two_projective_lintegral f g hg]
  congr 1
  · apply lintegral_congr
    intro x
    exact (affineEpigraph_projective_isometry_area_density hΩ hcv hu hp a L hD hK hzero
      hs bS (flatProductFiberBasis bF f) bRef f (flatProductFiberBasis_last bF f) x).symm
  · apply lintegral_congr
    intro x
    exact (affineEpigraph_projective_isometry_area_density hΩ hcv hu hp a L hD hK hzero
      hs bS (flatProductFiberBasis bF (f.trans (LinearIsometryEquiv.neg ℝ))) bRef
      (f.trans (LinearIsometryEquiv.neg ℝ)) (flatProductFiberBasis_last bF _) x).symm

end WholeSphereArea

-- ProductAreaChart

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WholeGraphAreaTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section WholeGraphAreaTransport
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Full graph-area transport above a regular fiber base. The loss is a fixed
finite chart multiplicity, chosen before every varying epigraph and affine map.
No surjectivity or area transport law is assumed. -/
theorem affineEpigraph_whole_graph_area_bound_oai {n : ℕ}
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
    ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
    (∀ x ∈ Ω, (hessian u x).PosDef) →
    ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
      {D : Set S}, IsOpen D →
    (∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    (∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ D →
    ∀ {K : Set (Space n)}, K ⊆ Ω →
    (∀ x ∈ K, (L.symm ((x,u x)-a)).1 ∈ Q) →
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.toBasis.prod bRef.toBasis).reindex eA.symm
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
      ((n:ℝ)/((n:ℝ)+2))) *
        (∫⁻ x in K, ENNReal.ofReal (affineAreaDensity u x)) ≤
    ENNReal.ofReal C * (∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
      ENNReal.ofReal (Real.rpow (tubeBaseMatrix H (s,v) bS.toBasis).det δ *
        Real.rpow (tubeAngularDensity H (s,v) bRef) (1-δ)) ∂volume.toSphere) := by
  let J := (κ ⊕ Unit) × Bool
  let frame : J → WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E := signedProjectiveFrame bRef f
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let b := (bS.toBasis.prod bRef.toBasis).reindex eA.symm
  let bj (j : J) := (bS.toBasis.prod (flatProductFiberBasis bF (frame j)).toBasis).reindex eA.symm
  let d (j : J) : ℝ := Real.rpow |b.det (bj j)| ((n:ℝ)/((n:ℝ)+2))
  let C : ℝ := 1 + ∑ j, d j
  have hd (j : J) : 0 ≤ d j := Real.rpow_nonneg (abs_nonneg _) _
  have hC : 0 < C := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => hd j))
  refine ⟨C,hC,?_⟩
  intro Ω hΩ hcv u hu hp a L D hD hK hzero Q hQ hQD K hKO hKQ
  dsimp only
  let Z := flatProductCoordinates bS bF e
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
  let A : ℝ≥0∞ := ∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
    ENNReal.ofReal (Real.rpow (tubeBaseMatrix H (s,v) bS.toBasis).det δ *
      Real.rpow (tubeAngularDensity H (s,v) bRef) (1-δ)) ∂volume.toSphere
  let Dref : ℝ := Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
    ((n:ℝ)/((n:ℝ)+2))
  let Dj (j : J) : ℝ := Real.rpow |(bj j).det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
    ((n:ℝ)/((n:ℝ)+2))
  have hdet (j : J) : Dref = d j * Dj j := by
    dsimp only [Dref,d,Dj]
    rw [← b.det_mul_det (bj j),abs_mul]
    simp only [Real.rpow_eq_pow]
    exact Real.mul_rpow (abs_nonneg _) (abs_nonneg _)
  choose φ hsource htarget hφ harea using fun j : J =>
    affineEpigraph_product_area_chart hΩ hcv hu hp a L hD hK hzero bS bF (frame j) e
  let T (j : J) := φ j '' (Z ⁻¹' (Q ×ˢ Set.univ))
  have hcover : K ⊆ ⋃ j, T j := by
    intro x hx
    let p := L.symm ((x,u x)-a)
    have hpa : a+L p = (x,u x) := by simp [p]
    have hpD : p.1 ∈ D := hQD (hKQ x hx)
    have hpΩ : (a+L (p.1,p.2)).1 ∈ Ω := by rw [Prod.mk.eta,hpa]; exact hKO hx
    have hpF : affineDefining u a L (p.1,p.2) = 0 := by
      change u (a+L p).1 - (a+L p).2 = 0
      rw [hpa]; simp
    have hg := affineEpigraph_gauss_surjective hΩ hcv hu hp a L hD hK hzero hpD hpΩ hpF
    dsimp only at hg
    obtain ⟨j,hj⟩ := signedProjectiveFrame_cover bRef f hg.1
    apply Set.mem_iUnion.mpr
    refine ⟨j,?_⟩
    have hh := flatGraphChart_covers_direction Ω u a L bS bF (frame j) e (φ j)
      (hsource j) (hφ j) hQD (hKQ x hx) hg.2 hj
    change (a+L p).1 ∈ T j at hh
    rw [hpa] at hh
    exact hh
  have hchart (j : J) : ENNReal.ofReal (Dj j) *
      (∫⁻ x in T j, ENNReal.ofReal (affineAreaDensity u x)) ≤ A := by
    rw [harea j hQ hQD]
    refine (lintegral_prod_le _).trans ?_
    apply setLIntegral_mono_ae' hQ
    filter_upwards with s hs
    have he := affineEpigraph_sphere_area_two_flat_lintegral hΩ hcv hu hp a L hD hK hzero
      (hQD hs) bS.toBasis bF bRef (frame j)
    exact (he.symm ▸ le_add_right le_rfl)
  have hchart' (j : J) : ENNReal.ofReal Dref *
      (∫⁻ x in T j, ENNReal.ofReal (affineAreaDensity u x)) ≤ ENNReal.ofReal (d j)*A := by
    rw [hdet j,ENNReal.ofReal_mul (hd j),mul_assoc]
    exact mul_le_mul_right (hchart j) _
  change ENNReal.ofReal Dref * (∫⁻ x in K, ENNReal.ofReal (affineAreaDensity u x)) ≤ ENNReal.ofReal C*A
  calc
    _ ≤ ENNReal.ofReal Dref * (∫⁻ x in ⋃ j, T j, ENNReal.ofReal (affineAreaDensity u x)) :=
      mul_le_mul_right (lintegral_mono_set hcover) _
    _ ≤ ENNReal.ofReal Dref * ∑ j, ∫⁻ x in T j, ENNReal.ofReal (affineAreaDensity u x) := by
      apply mul_le_mul_right
      simpa only [tsum_fintype] using lintegral_iUnion_le T (fun x => ENNReal.ofReal (affineAreaDensity u x))
    _ = ∑ j, ENNReal.ofReal Dref * ∫⁻ x in T j, ENNReal.ofReal (affineAreaDensity u x) := by rw [Finset.mul_sum]
    _ ≤ ∑ j, ENNReal.ofReal (d j)*A := Finset.sum_le_sum (fun j _ => hchart' j)
    _ = (∑ j, ENNReal.ofReal (d j))*A := by rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal C*A := by
      apply mul_le_mul_left
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hd j)]
      exact ENNReal.ofReal_le_ofReal (by dsimp only [C]; linarith)
end WholeGraphAreaTransport

-- ActualAreaMass

end
end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound_oai.{u_1, u_2, u_3, u_4, u_5}
