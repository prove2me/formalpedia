-- Prove2me | solution 1 for IntLInfty.Kan.crForms_exterior_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:57:13.963261+00:00
-- url     : https://prove2.me/submissions/8cfa2707-84cd-4d5c-8232-8d11b2518610

import Mathlib
import Definitions.Def_IntLInfty_Kan_Forms

set_option autoImplicit false
set_option maxHeartbeats 400000


namespace IntLInfty.Kan.A83D2

open MeasureTheory Filter Topology
open scoped ContDiff

variable {m : ℕ}

theorem cont_mul_test {U : Set (Fin m → ℝ)} (hU : IsOpen U) {f φ : (Fin m → ℝ) → ℝ}
    (hf : ContinuousOn f U) (hφ : Continuous φ) (hφU : tsupport φ ⊆ U) :
    Continuous (fun x => f x * φ x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (hf.continuousAt (hU.mem_nhds hx)).mul hφ.continuousAt
  · have h0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hφU h))
    have h1 : (fun y => f y * φ y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      h0.mono fun y hy => by simp [hy]
    exact (continuousAt_const).congr h1.symm

theorem integ_test {U : Set (Fin m → ℝ)} (hU : IsOpen U) {f φ : (Fin m → ℝ) → ℝ}
    (hf : ContinuousOn f U) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) : Integrable (fun x => f x * φ x) :=
  (cont_mul_test hU hf hφ hφU).integrable_of_hasCompactSupport hφc.mul_left

/-- Integration by parts against a test function supported in `U`, for `g` only `C¹` on `U`. -/
theorem ibp {U : Set (Fin m → ℝ)} (hU : IsOpen U) {g ψ : (Fin m → ℝ) → ℝ}
    (hg : ContDiffOn ℝ 1 g U) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (v : Fin m → ℝ) :
    ∫ x, fderiv ℝ g x v * ψ x = - ∫ x, g x * fderiv ℝ ψ x v := by
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := g) (g := ψ)
    (v := v)
    (integ_test hU ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)
      hψ.continuous hψc hψU)
    (integ_test hU hg.continuousOn hdψ (hψc.fderiv_apply ℝ v)
      ((tsupport_fderiv_apply_subset ℝ v).trans hψU))
    (integ_test hU hg.continuousOn hψ.continuous hψc hψU)
    (fun x hx => ((hg.differentiableOn one_ne_zero) x (hψU hx)).differentiableAt (hU.mem_nhds (hψU hx)))
    (fun x _ => (hψ.differentiable one_ne_zero) x)
  rw [h, neg_neg]

/-- Weak `d² = 0`: if the coefficients `c J` are `C¹` on an open `U` and the coefficients
`η K = ∑ s k J K ∂ₖ c J` of `dω` are `C¹` on `U`, then the coefficients of `d(dω)` vanish on `U`,
provided the structure constants are antisymmetric (`dxₗ ∧ dxₖ = - dxₖ ∧ dxₗ`). -/
theorem dd_zero_open {U : Set (Fin m → ℝ)} (hU : IsOpen U) {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → (Fin m → ℝ) → ℝ) (hc : ∀ J, ContDiffOn ℝ 1 (c J) U)
    (s : Fin m → ι → κ → ℝ) (t : Fin m → κ → ℝ)
    (η : κ → (Fin m → ℝ) → ℝ) (hη : ∀ K, ContDiffOn ℝ 1 (η K) U)
    (hηeq : ∀ K, ∀ x ∈ U, η K x = ∑ k, ∑ J, fderiv ℝ (c J) x (Pi.single k 1) * s k J K)
    (hanti : ∀ l k J, ∑ K, t l K * s k J K = - ∑ K, t k K * s l J K) :
    ∀ x ∈ U, ∑ l, ∑ K, fderiv ℝ (η K) x (Pi.single l 1) * t l K = 0 := by
  set e : Fin m → (Fin m → ℝ) := fun k => Pi.single k 1 with he
  set G : (Fin m → ℝ) → ℝ := fun x => ∑ l, ∑ K, fderiv ℝ (η K) x (e l) * t l K with hG
  have hdη : ∀ K l, ContinuousOn (fun x => fderiv ℝ (η K) x (e l)) U := fun K l =>
    ((hη K).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hdc : ∀ J k, ContinuousOn (fun x => fderiv ℝ (c J) x (e k)) U := fun J k =>
    ((hc J).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hGc : ContinuousOn G U := by
    refine continuousOn_finsetSum _ fun l _ => continuousOn_finsetSum _ fun K _ => ?_
    exact (hdη K l).mul continuousOn_const
  -- the test-function identity
  have key : ∀ ψ : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ψ x • G x = 0 := by
    intro ψ hψ hψc hψU
    have hψ1 : ContDiff ℝ 1 ψ := contDiff_infty.1 hψ 1
    have hψ2 : ContDiff ℝ 2 ψ := contDiff_infty.1 hψ 2
    -- first derivatives of ψ
    set D : Fin m → (Fin m → ℝ) → ℝ := fun l x => fderiv ℝ ψ x (e l) with hD
    have hD1 : ∀ l, ContDiff ℝ 1 (D l) := fun l =>
      (hψ2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hDc : ∀ l, HasCompactSupport (D l) := fun l => hψc.fderiv_apply ℝ (e l)
    have hDU : ∀ l, tsupport (D l) ⊆ U := fun l => (tsupport_fderiv_apply_subset ℝ (e l)).trans hψU
    -- second derivatives, symmetric
    set A : Fin m → Fin m → ι → ℝ := fun k l J => ∫ x, c J x * fderiv ℝ (D l) x (e k) with hA
    have hsymm : ∀ k l J, A k l J = A l k J := by
      intro k l J
      simp only [hA]
      congr 1
      ext x
      congr 1
      have hs := (hψ2.contDiffAt (x := x)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
      have h1 : ∀ a b, fderiv ℝ (D a) x (e b) = fderiv ℝ (fderiv ℝ ψ) x (e b) (e a) := by
        intro a b
        have hdiff : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
          ((hψ2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
        simp only [hD]
        rw [fderiv_clm_apply hdiff (differentiableAt_const _)]
        simp
      rw [h1, h1, hs]
    -- per-term identity
    have hP : ∀ l K, ∫ x, fderiv ℝ (η K) x (e l) * ψ x = ∑ k, ∑ J, s k J K * A k l J := by
      intro l K
      rw [ibp hU (hη K) hψ1 hψc hψU (e l)]
      have hcongr : (fun x => η K x * fderiv ℝ ψ x (e l)) =
          fun x => ∑ k, ∑ J, s k J K * (fderiv ℝ (c J) x (e k) * D l x) := by
        ext x
        by_cases hx : x ∈ U
        · rw [hηeq K x hx, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun J _ => ?_
          simp only [hD, he]
          ring
        · have h0 : D l x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hDU l h))
          have h0' : fderiv ℝ ψ x (e l) = 0 := h0
          simp [h0, h0']
      rw [hcongr]
      have hint : ∀ k J, Integrable (fun x => fderiv ℝ (c J) x (e k) * D l x) := fun k J =>
        integ_test hU (hdc J k) (hD1 l).continuous (hDc l) (hDU l)
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun J _ => (hint k J).const_mul _)]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ (fun J _ => (hint k J).const_mul _), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [integral_const_mul, ibp hU (hc J) (hD1 l) (hDc l) (hDU l) (e k)]
      simp only [hA]
      ring
    -- assemble
    have hcongr2 : (fun x => ψ x • G x) =
        fun x => ∑ l, ∑ K, t l K * (fderiv ℝ (η K) x (e l) * ψ x) := by
      ext x
      simp only [hG, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun K _ => ?_
      ring
    have hint2 : ∀ l K, Integrable (fun x => fderiv ℝ (η K) x (e l) * ψ x) := fun l K =>
      integ_test hU (hdη K l) hψ.continuous hψc hψU
    rw [hcongr2, integral_finsetSum _ (fun l _ => integrable_finsetSum _ fun K _ =>
      (hint2 l K).const_mul _)]
    simp_rw [integral_finsetSum _ (fun K _ => (hint2 _ K).const_mul _), integral_const_mul, hP]
    -- antisymmetry kills the sum
    have hre : ∑ l, ∑ K, t l K * ∑ k, ∑ J, s k J K * A k l J
        = ∑ l, ∑ k, ∑ J, (∑ K, t l K * s k J K) * A k l J := by
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun K _ => by ring
    rw [hre]
    set S := ∑ l, ∑ k, ∑ J, (∑ K, t l K * s k J K) * A k l J with hS
    have hSS : S = -S := by
      conv_lhs => rw [hS, Finset.sum_comm]
      rw [hS, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [hanti k l J, hsymm l k J]
      ring
    linarith
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hGc.locallyIntegrableOn hU.measurableSet) key
  have hae' : G =ᵐ[volume.restrict U] 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
    exact hae
  have heq := Measure.eqOn_open_of_ae_eq hae' hU hGc continuousOn_const
  intro x hx
  exact heq hx

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

theorem coeff_add {m : ℕ} (ω ω' : Ω m) (I : Finset (Fin m)) :
    coeff (ω + ω') I = coeff ω I + coeff ω' I := by
  funext x; simp [coeff]

theorem coeff_smul {m : ℕ} (c : ℝ) (ω : Ω m) (I : Finset (Fin m)) :
    coeff (c • ω) I = c • coeff ω I := by
  funext x; simp [coeff]

theorem jetComp_congr {m k : ℕ} {f g : (Fin m → ℝ) → ℝ} (h : Set.EqOn f g (simplex m))
    (β : Fin k → Fin m) : jetComp f k β = jetComp g k β := by
  have he : Set.EqOn (fun x => iteratedFDerivWithin ℝ k f (simplex m) x fun l => Pi.single (β l) 1)
      (fun x => iteratedFDerivWithin ℝ k g (simplex m) x fun l => Pi.single (β l) 1) (simplex m) :=
    fun x hx => by simp only [iteratedFDerivWithin_congr h hx]
  unfold jetComp
  split_ifs with h1 h2 h2
  · ext x; simp [BoundedContinuousFunction.mkOfCompact_apply, he x.2]
  · exact absurd (h1.congr he.symm) h2
  · exact absurd (h2.congr he) h1
  · rfl

theorem contOn_iter {m k r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) (hk : k ≤ r)
    (β : Fin k → Fin m) :
    ContinuousOn (fun x => iteratedFDerivWithin ℝ k f (simplex m) x fun l => Pi.single (β l) 1)
      (simplex m) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin m → ℝ) ℝ
      (fun l => Pi.single (β l) 1)).continuous.comp_continuousOn
    (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_simplex m))

theorem jetComp_add {m k r : ℕ} {f g : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m))
    (hg : ContDiffOn ℝ r g (simplex m)) (hk : k ≤ r) (β : Fin k → Fin m) :
    jetComp (f + g) k β = jetComp f k β + jetComp g k β := by
  have hfk : ContDiffOn ℝ k f (simplex m) := hf.of_le (by exact_mod_cast hk)
  have hgk : ContDiffOn ℝ k g (simplex m) := hg.of_le (by exact_mod_cast hk)
  unfold jetComp
  rw [dif_pos (contOn_iter (f := f + g) (hf.add hg) hk β), dif_pos (contOn_iter hf hk β),
    dif_pos (contOn_iter hg hk β)]
  ext x
  simp only [BoundedContinuousFunction.mkOfCompact_apply, BoundedContinuousFunction.coe_add,
    Pi.add_apply, ContinuousMap.coe_mk]
  change (iteratedFDerivWithin ℝ k (f + g) (simplex m) x.1) _ =
    (iteratedFDerivWithin ℝ k f (simplex m) x.1) _ + (iteratedFDerivWithin ℝ k g (simplex m) x.1) _
  rw [iteratedFDerivWithin_add_apply (hfk x.1 x.2) (hgk x.1 x.2) (uniqueDiffOn_simplex m) x.2]
  rfl

theorem jetComp_smul {m k r : ℕ} (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m))
    (hk : k ≤ r) (β : Fin k → Fin m) :
    jetComp (c • f) k β = c • jetComp f k β := by
  have hfk : ContDiffOn ℝ k f (simplex m) := hf.of_le (by exact_mod_cast hk)
  unfold jetComp
  rw [dif_pos (contOn_iter (f := c • f) (hf.const_smul c) hk β), dif_pos (contOn_iter hf hk β)]
  ext x
  simp only [BoundedContinuousFunction.mkOfCompact_apply, BoundedContinuousFunction.coe_smul,
    ContinuousMap.coe_mk]
  change (iteratedFDerivWithin ℝ k (c • f) (simplex m) x.1) _ =
    c • (iteratedFDerivWithin ℝ k f (simplex m) x.1) _
  rw [iteratedFDerivWithin_const_smul_apply (hfk x.1 x.2) (uniqueDiffOn_simplex m) x.2]
  rfl

end FormsLin

section FormsLin2

variable {m r : ℕ}

theorem extD_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (ω + ω') x = extD ω x + extD ω' x := by
  have hd : ∀ η : Ω m, IsCr r η → ∀ I, DifferentiableWithinAt ℝ (coeff η I) (simplex m) x :=
    fun η h I => ((h I).1.differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) x hx
  simp only [extD, coeff_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [fderivWithin_add (uniqueDiffOn_simplex m x hx) (hd ω hω I) (hd ω' hω' I)]
  simp [add_smul]

theorem extD_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (c • ω) x = c • extD ω x := by
  have hd : ∀ I, DifferentiableWithinAt ℝ (coeff ω I) (simplex m) x :=
    fun I => ((hω I).1.differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) x hx
  have e : ∀ I, fderivWithin ℝ (c • coeff ω I) (simplex m) x =
      c • fderivWithin ℝ (coeff ω I) (simplex m) x :=
    fun I => fderivWithin_const_smul (uniqueDiffOn_simplex m x hx) (hd I) c
  simp only [extD, coeff_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_smul_comm, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [e I, ContinuousLinearMap.smul_apply, smul_assoc]

theorem isDeg_add {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω') : IsDeg n (ω + ω') :=
  fun x hx => Submodule.add_mem _ (h x hx) (h' x hx)

theorem isDeg_smul {n : ℕ} (c : ℝ) {ω : Ω m} (h : IsDeg n ω) : IsDeg n (c • ω) :=
  fun x hx => Submodule.smul_mem _ c (h x hx)

theorem isCr_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') : IsCr r (ω + ω') := by
  intro I
  refine ⟨by rw [coeff_add]; exact (hω I).1.add (hω' I).1, ((hω I).2.add (hω' I).2).congr ?_⟩
  intro x hx
  show (formBasis m).repr (extD (ω + ω') x) I = coeff (extD ω) I x + coeff (extD ω') I x
  rw [extD_add hr hω hω' hx, map_add]; rfl

theorem isCr_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) : IsCr r (c • ω) := by
  intro I
  refine ⟨by rw [coeff_smul]; exact (hω I).1.const_smul c, ((hω I).2.const_smul c).congr ?_⟩
  intro x hx
  show (formBasis m).repr (extD (c • ω) x) I = c • coeff (extD ω) I x
  rw [extD_smul hr c hω hx, map_smul]; rfl

theorem jet_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') :
    jet r (ω + ω') = jet r ω + jet r ω' := by
  refine Prod.ext (funext fun I => funext fun k => funext fun β => ?_)
    (funext fun I => funext fun k => funext fun β => ?_)
  · show jetComp (coeff (ω + ω') I) k β = jetComp (coeff ω I) k β + jetComp (coeff ω' I) k β
    rw [coeff_add, jetComp_add (hω I).1 (hω' I).1 (Nat.lt_succ_iff.mp k.2)]
  · show jetComp (coeff (extD (ω + ω')) I) k β =
      jetComp (coeff (extD ω) I) k β + jetComp (coeff (extD ω') I) k β
    rw [jetComp_congr (g := coeff (extD ω) I + coeff (extD ω') I) (fun x hx => by
        show (formBasis m).repr (extD (ω + ω') x) I = coeff (extD ω) I x + coeff (extD ω') I x
        rw [extD_add hr hω hω' hx, map_add]; rfl),
      jetComp_add (hω I).2 (hω' I).2 (Nat.lt_succ_iff.mp k.2)]

theorem jet_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) :
    jet r (c • ω) = c • jet r ω := by
  refine Prod.ext (funext fun I => funext fun k => funext fun β => ?_)
    (funext fun I => funext fun k => funext fun β => ?_)
  · show jetComp (coeff (c • ω) I) k β = c • jetComp (coeff ω I) k β
    rw [coeff_smul, jetComp_smul c (hω I).1 (Nat.lt_succ_iff.mp k.2)]
  · show jetComp (coeff (extD (c • ω)) I) k β = c • jetComp (coeff (extD ω) I) k β
    rw [jetComp_congr (g := c • coeff (extD ω) I) (fun x hx => by
        show (formBasis m).repr (extD (c • ω) x) I = c • coeff (extD ω) I x
        rw [extD_smul hr c hω hx, map_smul]; rfl),
      jetComp_smul c (hω I).2 (Nat.lt_succ_iff.mp k.2)]

theorem isCr_zero : IsCr r (0 : Ω m) := by
  intro I
  have h0 : ∀ J, coeff (0 : Ω m) J = fun _ => 0 := by intro J; funext x; simp [coeff]
  have h1 : extD (0 : Ω m) = 0 := by funext x; simp [extD, h0]
  refine ⟨by rw [h0]; exact contDiffOn_const, by rw [h1, h0]; exact contDiffOn_const⟩

theorem isDeg_zero {n : ℕ} : IsDeg n (0 : Ω m) := fun _ _ => Submodule.zero_mem _

/-- The span in the definition of `CrForms` adds nothing: it is already the image of the jet map. -/
theorem span_jet_eq (hr : 1 ≤ r) (n : ℕ) :
    ((Submodule.span ℝ (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) : Submodule ℝ _) :
      Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} := by
  refine le_antisymm (fun w hw => ?_) Submodule.subset_span
  induction hw using Submodule.span_induction with
  | mem y hy => exact hy
  | zero =>
    refine ⟨0, ⟨isDeg_zero, isCr_zero⟩, ?_⟩
    have := jet_smul (m := m) hr 0 (isCr_zero (m := m) (r := r))
    simpa using this
  | add a b _ _ ha hb =>
    obtain ⟨ω, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ω', ⟨h1', h2'⟩, rfl⟩ := hb
    exact ⟨ω + ω', ⟨isDeg_add h1 h1', isCr_add hr h2 h2'⟩, jet_add hr h2 h2'⟩
  | smul c a _ ha =>
    obtain ⟨ω, ⟨h1, h2⟩, rfl⟩ := ha
    exact ⟨c • ω, ⟨isDeg_smul c h1, isCr_smul hr c h2⟩, jet_smul hr c h2⟩

theorem crForms_coe (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = closure (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) := by
  rw [CrForms, Submodule.topologicalClosure_coe, span_jet_eq hr n]

end FormsLin2

open Filter Topology

section TaylorLimit

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tendstoUniformlyOn_curryLeft {S : Set E} {j : ℕ}
    {q : ℕ → E → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F}
    {Q : E → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F}
    (h : TendstoUniformlyOn q Q atTop S) :
    TendstoUniformlyOn (fun k x => (q k x).curryLeft) (fun x => (Q x).curryLeft) atTop S := by
  have hu : UniformContinuous
      (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F => A.curryLeft) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).isometry.uniformContinuous
  exact hu.comp_tendstoUniformlyOn h

theorem taylor_limit {S : Set E} (hconv : Convex ℝ S) (hcl : closure (interior S) = S) {r : ℕ}
    {f : ℕ → E → F} {p : ℕ → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ k, HasFTaylorSeriesUpToOn r (f k) (p k) S)
    {P : E → FormalMultilinearSeries ℝ E F}
    (hP : ∀ j ≤ r, TendstoUniformlyOn (fun k x => p k x j) (fun x => P x j) atTop S) :
    HasFTaylorSeriesUpToOn r (fun x => (P x 0).curry0) P S := by
  have hcont : ∀ j ≤ r, ContinuousOn (fun x => P x j) S := fun j hj =>
    (hP j hj).continuousOn (Eventually.frequently (Eventually.of_forall fun k =>
      (hp k).cont j (by exact_mod_cast hj)))
  refine ⟨fun x _ => rfl, ?_, fun j hj => hcont j (by exact_mod_cast hj)⟩
  intro j hj x hx
  have hj' : j + 1 ≤ r := by exact_mod_cast hj
  set s := interior S with hs_def
  have hso : IsOpen s := isOpen_interior
  have hsc : Convex ℝ s := hconv.interior
  have hsS : s ⊆ S := interior_subset
  have hder : ∀ y ∈ s, HasFDerivAt (fun x => P x j) (P y (j + 1)).curryLeft y := by
    intro y hy
    refine hasFDerivAt_of_tendstoUniformlyOn (l := atTop) hso
      (f := fun k x => p k x j) (f' := fun k x => (p k x (j + 1)).curryLeft)
      ((tendstoUniformlyOn_curryLeft ((hP (j + 1) hj').mono hsS))) ?_ ?_ hy
    · intro k z hz
      exact ((hp k).fderivWithin j (by exact_mod_cast hj) z (hsS hz)).hasFDerivAt
        (mem_interior_iff_mem_nhds.mp hz)
    · intro z hz
      exact (hP j (by omega)).tendsto_at (hsS hz)
  have hG'cont : ContinuousOn (fun x => (P x (j + 1)).curryLeft) S := by
    have := hcont (j + 1) hj'
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).continuous.comp_continuousOn
      this
  have key := hasFDerivWithinAt_closure_of_tendsto_fderiv (f := fun x => P x j)
    (f' := (P x (j + 1)).curryLeft) (x := x)
    (fun y hy => (hder y hy).differentiableAt.differentiableWithinAt) hsc hso
    (fun y hy => by
      rw [hcl] at hy
      exact ((hcont j (by omega)) y hy).mono hsS)
    (by
      have h1 : Tendsto (fun y => (P y (j + 1)).curryLeft) (𝓝[s] x) (𝓝 (P x (j + 1)).curryLeft) :=
        ((hG'cont x hx).mono hsS).tendsto
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hder y hy).fderiv.symm)
  rwa [hcl] at key

end TaylorLimit

section JetLimit

open IntLInfty.Kan BoundedContinuousFunction

theorem isClosed_simplex (m : ℕ) : IsClosed (simplex m) := by
  have h1 : IsClosed {t : Fin m → ℝ | ∀ i, 0 ≤ t i} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {t : Fin m → ℝ | ∑ i, t i ≤ 1} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

theorem closure_interior_simplex (m : ℕ) : closure (interior (simplex m)) = simplex m := by
  rw [(convex_simplex m).closure_interior_eq_closure_of_nonempty_interior
    (interior_simplex_nonempty m)]
  exact (isClosed_simplex m).closure_eq

theorem jetComp_apply {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
    (hk : k ≤ r) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f k β ⟨x, hx⟩ = iteratedFDerivWithin ℝ k f (simplex m) x (fun l => Pi.single (β l) 1) := by
  unfold jetComp
  rw [dif_pos (contOn_iter hf hk β)]
  rfl

theorem norm_cmm_le_sum {m j : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin m → ℝ) ℝ) :
    ‖M‖ ≤ ∑ β : Fin j → Fin m, |M (fun l => Pi.single (β l) 1)| := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun v => ?_
  have hv : v = fun l => ∑ i : Fin m, v l i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    funext l; ext t; simp [Finset.sum_apply, Pi.single_apply]
  have hexp : M v = ∑ β : Fin j → Fin m, (∏ l, v l (β l)) • M (fun l => Pi.single (β l) 1) := by
    conv_lhs => rw [hv]
    rw [M.map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    exact M.map_smul_univ _ _
  rw [hexp, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [norm_smul, norm_prod, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun l _ => norm_le_pi_norm (v l) (β l)) (abs_nonneg _)

/-- Sub-lemma A: a limit (in the jet norm) of jets of `Cʳ` functions on the simplex is the jet of a
`Cʳ` function. -/
theorem jet_limit {m r : ℕ} {f : ℕ → (Fin m → ℝ) → ℝ} (hf : ∀ k, ContDiffOn ℝ r (f k) (simplex m))
    {g : (j : Fin (r + 1)) → (Fin (j : ℕ) → Fin m) → (simplex m →ᵇ ℝ)}
    (hg : ∀ (j : Fin (r + 1)) β, Tendsto (fun k => jetComp (f k) j β) atTop (𝓝 (g j β))) :
    ∃ F : (Fin m → ℝ) → ℝ, ContDiffOn ℝ r F (simplex m) ∧
      ∀ (j : Fin (r + 1)) β, jetComp F j β = g j β := by
  have hU : UniqueDiffOn ℝ (simplex m) := uniqueDiffOn_simplex m
  have hCau : ∀ j : Fin (r + 1),
      UniformCauchySeqOn (fun k x => iteratedFDerivWithin ℝ j (f k) (simplex m) x) atTop (simplex m) := by
    intro j
    let J : ℕ → (Fin (j : ℕ) → Fin m) → (simplex m →ᵇ ℝ) := fun k β => jetComp (f k) j β
    have hJ : Tendsto J atTop (𝓝 fun β => g j β) := tendsto_pi_nhds.mpr fun β => hg j β
    have hJc := hJ.cauchySeq
    rw [Metric.cauchySeq_iff] at hJc
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set c : ℝ := (Fintype.card (Fin (j : ℕ) → Fin m) : ℝ) + 1 with hc_def
    have hc : 0 < c := by positivity
    obtain ⟨N, hN⟩ := hJc (ε / c) (div_pos hε hc)
    refine ⟨N, fun a ha b hb x hx => ?_⟩
    have hab := hN a ha b hb
    rw [dist_eq_norm] at hab ⊢
    refine lt_of_le_of_lt (norm_cmm_le_sum _) ?_
    have hterm : ∀ β : Fin (j : ℕ) → Fin m,
        |(iteratedFDerivWithin ℝ j (f a) (simplex m) x - iteratedFDerivWithin ℝ j (f b) (simplex m) x)
          (fun l => Pi.single (β l) 1)| ≤ ε / c := by
      intro β
      rw [_root_.sub_apply, ← jetComp_apply (hf a) (Fin.is_le j) β hx,
        ← jetComp_apply (hf b) (Fin.is_le j) β hx]
      calc |jetComp (f a) j β ⟨x, hx⟩ - jetComp (f b) j β ⟨x, hx⟩|
          = ‖(J a β - J b β) ⟨x, hx⟩‖ := by rw [Real.norm_eq_abs]; rfl
        _ ≤ ‖J a β - J b β‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
        _ ≤ ‖J a - J b‖ := norm_le_pi_norm (J a - J b) β
        _ ≤ ε / c := hab.le
    calc ∑ β : Fin (j : ℕ) → Fin m, |(iteratedFDerivWithin ℝ j (f a) (simplex m) x -
          iteratedFDerivWithin ℝ j (f b) (simplex m) x) (fun l => Pi.single (β l) 1)|
        ≤ ∑ _β : Fin (j : ℕ) → Fin m, ε / c := Finset.sum_le_sum fun β _ => hterm β
      _ = (Fintype.card (Fin (j : ℕ) → Fin m) : ℝ) * (ε / c) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < c * (ε / c) := by
          apply mul_lt_mul_of_pos_right _ (div_pos hε hc)
          rw [hc_def]; linarith
      _ = ε := by field_simp
  let P : (Fin m → ℝ) → FormalMultilinearSeries ℝ (Fin m → ℝ) ℝ := fun x j =>
    limUnder atTop (fun k => iteratedFDerivWithin ℝ j (f k) (simplex m) x)
  have hPt : ∀ j : Fin (r + 1), ∀ x ∈ (simplex m),
      Tendsto (fun k => iteratedFDerivWithin ℝ j (f k) (simplex m) x) atTop (𝓝 (P x j)) :=
    fun j x hx => ((hCau j).cauchySeq hx).tendsto_limUnder
  have hP : ∀ j ≤ r, TendstoUniformlyOn (fun k x => ftaylorSeriesWithin ℝ (f k) (simplex m) x j)
      (fun x => P x j) atTop (simplex m) := by
    intro j hj
    exact (hCau ⟨j, Nat.lt_succ_of_le hj⟩).tendstoUniformlyOn_of_tendsto
      (hPt ⟨j, Nat.lt_succ_of_le hj⟩)
  have H := taylor_limit (convex_simplex m) (closure_interior_simplex m)
    (fun k => (hf k).ftaylorSeriesWithin hU) hP
  have hFc : ContDiffOn ℝ r (fun x => (P x 0).curry0) (simplex m) := H.contDiffOn
  refine ⟨fun x => (P x 0).curry0, hFc, fun j β => ?_⟩
  ext ⟨x, hx⟩
  rw [jetComp_apply hFc (Fin.is_le j) β hx,
    ← H.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast Fin.is_le j) hU hx]
  have h1 : Tendsto (fun k => jetComp (f k) j β ⟨x, hx⟩) atTop (𝓝 (g j β ⟨x, hx⟩)) :=
    ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (hg j β)
  have h2 : Tendsto (fun k => jetComp (f k) j β ⟨x, hx⟩) atTop
      (𝓝 (P x j (fun l => Pi.single (β l) 1))) := by
    have := ((continuous_eval_const (fun l => Pi.single (β l) (1 : ℝ))).tendsto
      _).comp (hPt j x hx)
    refine this.congr fun k => ?_
    exact (jetComp_apply (hf k) (Fin.is_le j) β hx).symm
  exact tendsto_nhds_unique h2 h1

end JetLimit

section JetClosed

open IntLInfty.Kan BoundedContinuousFunction

theorem jetComp_zero {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
    (hk : k = 0) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f k β ⟨x, hx⟩ = f x := by
  subst hk
  rw [jetComp_apply hf (Nat.zero_le _) β hx]
  rfl

theorem jetComp_one {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) (hr : 1 ≤ r)
    (β : Fin 1 → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f 1 β ⟨x, hx⟩ = fderivWithin ℝ f (simplex m) x (Pi.single (β 0) 1) := by
  rw [jetComp_apply hf hr β hx, iteratedFDerivWithin_one_apply (uniqueDiffOn_simplex m x hx)]

theorem continuous_jet_eval {r m : ℕ} (I : Finset (Fin m)) (j : Fin (r + 1))
    (β : Fin (j : ℕ) → Fin m) : Continuous (fun w : Jet r m => w I j β) := by
  have : Continuous (fun w : ((I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) →
      (simplex m →ᵇ ℝ)) => w I j β) :=
    (continuous_apply β).comp ((continuous_apply j).comp (continuous_apply I))
  exact this

theorem coeff_extD {m : ℕ} (ω : Ω m) (I : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (extD ω) I x = ∑ k : Fin m, ∑ J : Finset (Fin m),
      fderivWithin ℝ (coeff ω J) (simplex m) x (Pi.single k 1) *
        (formBasis m).repr (dx m k * formBasis m J) I := by
  simp only [coeff, extD, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem repr_dx_mul_expand {m : ℕ} (l : Fin m)
    (a : ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) (I : Finset (Fin m)) :
    ∑ K, (formBasis m).repr (dx m l * formBasis m K) I * (formBasis m).repr a K =
      (formBasis m).repr (dx m l * a) I := by
  conv_rhs => rw [← (formBasis m).sum_repr a]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun K _ => mul_comm _ _

theorem formBasis_anti {m : ℕ} (l k : Fin m) (J I : Finset (Fin m)) :
    ∑ K, (formBasis m).repr (dx m l * formBasis m K) I *
        (formBasis m).repr (dx m k * formBasis m J) K =
      - ∑ K, (formBasis m).repr (dx m k * formBasis m K) I *
        (formBasis m).repr (dx m l * formBasis m J) K := by
  rw [repr_dx_mul_expand, repr_dx_mul_expand, ← mul_assoc, ← mul_assoc]
  have h : dx m l * dx m k = -(dx m k * dx m l) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  rw [h, neg_mul, map_neg, Finsupp.neg_apply]

/-- `d² = 0` on the simplex for `Cʳ` forms (`r ≥ 1`), via the weak derivative. -/
theorem extD_extD {m r : ℕ} (hr : 1 ≤ r) {ω : Ω m} (hC : IsCr r ω) : IsClosedForm (extD ω) := by
  have hr' : (1 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hr
  have hcoef : ∀ I, ∀ y ∈ simplex m, coeff (extD (extD ω)) I y = 0 := by
    intro I
    have hF : ContinuousOn (coeff (extD (extD ω)) I) (simplex m) := by
      rw [show coeff (extD (extD ω)) I = fun y => ∑ k : Fin m, ∑ J : Finset (Fin m),
          fderivWithin ℝ (coeff (extD ω) J) (simplex m) y (Pi.single k 1) *
            (formBasis m).repr (dx m k * formBasis m J) I from funext (coeff_extD (extD ω) I)]
      refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun J _ => ?_
      exact (((hC J).2.continuousOn_fderivWithin (uniqueDiffOn_simplex m) hr').clm_apply
        continuousOn_const).mul continuousOn_const
    have hU0 : ∀ y ∈ interior (simplex m), coeff (extD (extD ω)) I y = 0 := by
      intro y hy
      have h := A83D2.dd_zero_open isOpen_interior (fun J => coeff ω J)
        (fun J => ((hC J).1.mono interior_subset).of_le hr')
        (fun k J K => (formBasis m).repr (dx m k * formBasis m J) K)
        (fun l K => (formBasis m).repr (dx m l * formBasis m K) I)
        (fun K => coeff (extD ω) K) (fun K => ((hC K).2.mono interior_subset).of_le hr') ?_
        (fun l k J => formBasis_anti l k J I) y hy
      · rw [coeff_extD]
        simp only [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hy)]
        exact h
      · intro K x hx
        rw [coeff_extD]
        simp only [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)]
    exact Set.EqOn.of_subset_closure (g := fun _ => (0 : ℝ)) hU0 hF continuousOn_const
      interior_subset (closure_interior_simplex m).symm.subset
  intro x hx
  exact (formBasis m).ext_elem fun I => by simpa [coeff] using hcoef I x hx

/-- A limit of jets of degree-`n` `Cʳ` forms is the jet of such a form `Ω0`; moreover the
coefficients of `d ω_k` converge pointwise on the simplex to those of `d Ω0`. -/
theorem jet_seq_limit {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) {ω : ℕ → Ω m}
    (hω : ∀ k, IsDeg n (ω k) ∧ IsCr r (ω k)) {w : ℕ → Jet r m × Jet r m}
    (hωw : ∀ k, jet r (ω k) = w k) {p : Jet r m × Jet r m} (hlim : Tendsto w atTop (𝓝 p)) :
    ∃ Ω0 : Ω m, (IsDeg n Ω0 ∧ IsCr r Ω0) ∧ jet r Ω0 = p ∧
      ∀ I, ∀ x ∈ simplex m, Tendsto (fun k => coeff (extD (ω k)) I x) atTop
        (𝓝 (coeff (extD Ω0) I x)) := by
  have h1 : ∀ I (j : Fin (r + 1)) β,
      Tendsto (fun k => jetComp (coeff (ω k) I) j β) atTop (𝓝 (p.1 I j β)) := by
    intro I j β
    have := ((((continuous_jet_eval I j β).comp continuous_fst)).tendsto p).comp hlim
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, ← hωw k, jet]
  have h2 : ∀ I (j : Fin (r + 1)) β,
      Tendsto (fun k => jetComp (coeff (extD (ω k)) I) j β) atTop (𝓝 (p.2 I j β)) := by
    intro I j β
    have := ((((continuous_jet_eval I j β).comp continuous_snd)).tendsto p).comp hlim
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, ← hωw k, jet]
  choose F hF hFj using fun I => jet_limit (fun k => ((hω k).2 I).1) (h1 I)
  choose G hG hGj using fun I => jet_limit (fun k => ((hω k).2 I).2) (h2 I)
  let Ω0 : Ω m := fun x => (formBasis m).equivFun.symm (fun I => F I x)
  have hcoeff : ∀ I, coeff Ω0 I = F I := by
    intro I; funext x
    show (formBasis m).repr ((formBasis m).equivFun.symm (fun I => F I x)) I = F I x
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let j0 : Fin (r + 1) := 0
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have hj0 : (j0 : ℕ) = 0 := rfl
  have hpt0 : ∀ I x (hx : x ∈ simplex m),
      Tendsto (fun k => coeff (ω k) I x) atTop (𝓝 (F I x)) := by
    intro I x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (h1 I j0 β0)
    rw [← hFj I j0 β0, jetComp_zero (hF I) hj0 β0 hx] at this
    refine this.congr fun k => ?_
    exact jetComp_zero ((hω k).2 I).1 hj0 β0 hx
  have hptG : ∀ I x (hx : x ∈ simplex m),
      Tendsto (fun k => coeff (extD (ω k)) I x) atTop (𝓝 (G I x)) := by
    intro I x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (h2 I j0 β0)
    rw [← hGj I j0 β0, jetComp_zero (hG I) hj0 β0 hx] at this
    refine this.congr fun k => ?_
    exact jetComp_zero ((hω k).2 I).2 hj0 β0 hx
  let j1 : Fin (r + 1) := ⟨1, by omega⟩
  have hpt1 : ∀ J (q : Fin m) x (hx : x ∈ simplex m),
      Tendsto (fun k => fderivWithin ℝ (coeff (ω k) J) (simplex m) x (Pi.single q 1)) atTop
        (𝓝 (fderivWithin ℝ (coeff Ω0 J) (simplex m) x (Pi.single q 1))) := by
    intro J q x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp
      (h1 J j1 (fun _ => q))
    rw [← hFj J j1 (fun _ => q)] at this
    have e1 : jetComp (F J) (j1 : ℕ) (fun _ => q) ⟨x, hx⟩ =
        fderivWithin ℝ (coeff Ω0 J) (simplex m) x (Pi.single q 1) := by
      rw [hcoeff J]; exact jetComp_one (hF J) hr (fun _ => q) hx
    rw [e1] at this
    refine this.congr fun k => ?_
    exact jetComp_one ((hω k).2 J).1 hr (fun _ => q) hx
  have hext : ∀ I, ∀ x ∈ simplex m, coeff (extD Ω0) I x = G I x := by
    intro I x hx
    have hA : Tendsto (fun k => coeff (extD (ω k)) I x) atTop (𝓝 (coeff (extD Ω0) I x)) := by
      simp only [coeff_extD]
      exact tendsto_finsetSum _ fun q _ => tendsto_finsetSum _ fun J _ =>
        (hpt1 J q x hx).mul_const _
    exact tendsto_nhds_unique hA (hptG I x hx)
  have hDeg : IsDeg n Ω0 := by
    intro x hx
    let W := (⋀[ℝ]^n (Module.Dual ℝ (Fin m → ℝ))).map
      (formBasis m).equivFun.toLinearMap
    have hWc : IsClosed (W : Set (Finset (Fin m) → ℝ)) := W.closed_of_finiteDimensional
    have hT : Tendsto (fun k => (formBasis m).equivFun (ω k x)) atTop (𝓝 fun I => F I x) := by
      refine tendsto_pi_nhds.mpr fun I => (hpt0 I x hx).congr fun k => ?_
      rw [Module.Basis.equivFun_apply]; rfl
    have hmem : (fun I => F I x) ∈ W := hWc.mem_of_tendsto hT
      (Eventually.of_forall fun k => Submodule.mem_map_of_mem ((hω k).1 x hx))
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp hmem
    have : Ω0 x = v := by
      show (formBasis m).equivFun.symm (fun I => F I x) = v
      rw [← hve]; exact LinearEquiv.symm_apply_apply _ v
    rw [this]; exact hv
  have hCr : IsCr r Ω0 := fun I =>
    ⟨(hcoeff I).symm ▸ hF I, (hG I).congr fun x hx => hext I x hx⟩
  refine ⟨Ω0, ⟨hDeg, hCr⟩, ?_, fun I x hx => by rw [hext I x hx]; exact hptG I x hx⟩
  refine Prod.ext ?_ ?_
  · show (fun I (k : Fin (r + 1)) β => jetComp (coeff Ω0 I) k β) = p.1
    funext I j β
    rw [hcoeff I, hFj I j β]
  · show (fun I (k : Fin (r + 1)) β => jetComp (coeff (extD Ω0) I) k β) = p.2
    funext I j β
    rw [jetComp_congr (hext I) β, hGj I j β]

theorem jetImage_closed {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    IsClosed (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) := by
  refine IsSeqClosed.isClosed fun w p hw hlim => ?_
  choose ω hω hωw using hw
  obtain ⟨Ω0, h0, hj, -⟩ := jet_seq_limit hr n hω hωw hlim
  exact ⟨Ω0, h0, hj⟩

theorem jetClosedImage_closed {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    IsClosed (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω}) := by
  refine IsSeqClosed.isClosed fun w p hw hlim => ?_
  choose ω hω hωw using hw
  obtain ⟨Ω0, ⟨hD, hC⟩, hj, ht⟩ :=
    jet_seq_limit hr n (fun k => ⟨(hω k).1, (hω k).2.1⟩) hωw hlim
  refine ⟨Ω0, ⟨hD, hC, fun x hx => ?_⟩, hj⟩
  have h0 : ∀ I, coeff (extD Ω0) I x = 0 := by
    intro I
    refine tendsto_nhds_unique (ht I x hx) ?_
    have hz : ∀ k, coeff (extD (ω k)) I x = 0 := fun k => by
      simp only [coeff, (hω k).2.2 x hx, map_zero, Finsupp.zero_apply]
    simp only [hz]; exact tendsto_const_nhds
  refine (formBasis m).ext_elem fun I => ?_
  rw [map_zero, Finsupp.zero_apply]
  exact h0 I

end JetClosed

theorem crForms_eq_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} := by
  rw [crForms_coe hr n, (jetImage_closed hr n).closure_eq]

section ClosedSpan

variable {m r : ℕ}

theorem isClosedForm_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
    (h : IsClosedForm ω) (h' : IsClosedForm ω') : IsClosedForm (ω + ω') := fun x hx => by
  rw [extD_add hr hω hω' hx, h x hx, h' x hx, add_zero]

theorem isClosedForm_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω)
    (h : IsClosedForm ω) : IsClosedForm (c • ω) := fun x hx => by
  rw [extD_smul hr c hω hx, h x hx, smul_zero]

theorem isClosedForm_zero : IsClosedForm (0 : Ω m) := by
  intro x _
  have h0 : ∀ J, coeff (0 : Ω m) J = fun _ => 0 := by intro J; funext x; simp [coeff]
  simp [extD, h0]

theorem span_jetClosed_eq (hr : 1 ≤ r) (n : ℕ) :
    ((Submodule.span ℝ (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω}) :
      Submodule ℝ _) : Set (Jet r m × Jet r m)) =
      jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω} := by
  refine le_antisymm (fun w hw => ?_) Submodule.subset_span
  induction hw using Submodule.span_induction with
  | mem y hy => exact hy
  | zero =>
    refine ⟨0, ⟨isDeg_zero, isCr_zero, isClosedForm_zero⟩, ?_⟩
    have := jet_smul (m := m) hr 0 (isCr_zero (m := m) (r := r))
    simpa using this
  | add a b _ _ ha hb =>
    obtain ⟨ω, ⟨h1, h2, h3⟩, rfl⟩ := ha
    obtain ⟨ω', ⟨h1', h2', h3'⟩, rfl⟩ := hb
    exact ⟨ω + ω', ⟨isDeg_add h1 h1', isCr_add hr h2 h2', isClosedForm_add hr h2 h2' h3 h3'⟩,
      jet_add hr h2 h2'⟩
  | smul c a _ ha =>
    obtain ⟨ω, ⟨h1, h2, h3⟩, rfl⟩ := ha
    exact ⟨c • ω, ⟨isDeg_smul c h1, isCr_smul hr c h2, isClosedForm_smul hr c h2 h3⟩,
      jet_smul hr c h2⟩

theorem crClosed_eq_image (hr : 1 ≤ r) (n : ℕ) :
    (CrClosed r m n : Set (Jet r m × Jet r m)) =
      jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω} := by
  rw [CrClosed, Submodule.topologicalClosure_coe, span_jetClosed_eq hr n,
    (jetClosedImage_closed hr n).closure_eq]

end ClosedSpan

section Rep

variable {m r : ℕ}

/-- Two forms agree on the simplex. -/
def FormEqOn (ω ω' : Ω m) : Prop := ∀ x ∈ simplex m, ω x = ω' x

theorem coeff_eqOn {ω ω' : Ω m} (h : FormEqOn ω ω') (I : Finset (Fin m)) :
    Set.EqOn (coeff ω I) (coeff ω' I) (simplex m) := fun x hx => by
  simp only [coeff, h x hx]

theorem extD_congr {ω ω' : Ω m} (h : FormEqOn ω ω') : FormEqOn (extD ω) (extD ω') := by
  intro x hx
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [fderivWithin_congr (coeff_eqOn h I) (coeff_eqOn h I hx)]

theorem jet_congr {ω ω' : Ω m} (h : FormEqOn ω ω') : jet r ω = jet r ω' := by
  have h1 : ∀ I, ∀ k (β : Fin k → Fin m),
      jetComp (coeff ω I) k β = jetComp (coeff ω' I) k β :=
    fun I _ β => jetComp_congr (coeff_eqOn h I) β
  have h2 : ∀ I, ∀ k (β : Fin k → Fin m),
      jetComp (coeff (extD ω) I) k β = jetComp (coeff (extD ω') I) k β :=
    fun I _ β => jetComp_congr (coeff_eqOn (extD_congr h) I) β
  simp only [jet, h1, h2]

theorem formEqOn_of_jet {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
    (h : jet r ω = jet r ω') : FormEqOn ω ω' := by
  intro x hx
  refine (formBasis m).ext_elem fun I => ?_
  let j0 : Fin (r + 1) := 0
  have hj0 : (j0 : ℕ) = 0 := rfl
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have e : (jet r ω).1 I j0 β0 = (jet r ω').1 I j0 β0 := by rw [h]
  simp only [jet] at e
  have e2 := congrArg (fun g : BoundedContinuousFunction (simplex m) ℝ => g ⟨x, hx⟩) e
  rw [jetComp_zero (hω I).1 hj0 β0 hx, jetComp_zero (hω' I).1 hj0 β0 hx] at e2
  exact e2

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

theorem coface_eq (i : Fin (m + 2)) (x : Fin m → ℝ) :
    coface m i x = vertex (m + 1) (i.succAbove 0) + ∑ k, x k •
      (vertex (m + 1) (i.succAbove k.succ) - vertex (m + 1) (i.succAbove 0)) := by
  funext a
  simp [coface, cofaceLin, Matrix.mulVec, dotProduct, mul_comm]

theorem coface_mem (i : Fin (m + 2)) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    coface m i x ∈ simplex (m + 1) := by
  let w : Fin (m + 1) → ℝ := Fin.cons (1 - ∑ k, x k) x
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ w j := by
    intro j _
    induction j using Fin.cases with
    | zero => simp only [w, Fin.cons_zero]; linarith [hx.2]
    | succ k => simp only [w, Fin.cons_succ]; exact hx.1 k
  have h1 : ∑ j, w j = 1 := by
    rw [Fin.sum_univ_succ]; simp only [w, Fin.cons_zero, Fin.cons_succ]; ring
  have hm := (convex_simplex (m + 1)).sum_mem h0 h1
    (z := fun j => vertex (m + 1) (i.succAbove j)) (fun j _ => vertex_mem _ _)
  convert hm using 1
  rw [coface_eq, Fin.sum_univ_succ]
  simp only [w, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul,
    one_smul, ← Finset.sum_smul]
  abel

theorem pull_congr (i : Fin (m + 2)) {ω ω' : Ω (m + 1)} (h : FormEqOn ω ω') :
    FormEqOn (pull m i ω) (pull m i ω') := fun x hx => by
  simp only [pull]; rw [h _ (coface_mem i hx)]

theorem viaRep_spec {m' n : ℕ} {V : Submodule ℝ (Jet r m' × Jet r m')} {F : Ω m → Ω m'}
    (hF : ∀ ω ω' : Ω m, FormEqOn ω ω' → FormEqOn (F ω) (F ω')) {ω : Ω m} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hV : jet r (F ω) ∈ V) :
    (viaRep n V F (jet r ω) : Jet r m' × Jet r m') = jet r (F ω) := by
  have hex : ∃ ω' : Ω m, IsDeg n ω' ∧ IsCr r ω' ∧ jet r ω' = jet r ω ∧ jet r (F ω') ∈ V :=
    ⟨ω, hD, hC, rfl, hV⟩
  simp only [viaRep, dif_pos hex]
  exact jet_congr (hF _ _ (formEqOn_of_jet hex.choose_spec.2.1 hC hex.choose_spec.2.2.1))

theorem faceCr_spec {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω)
    (hw : jet r ω ∈ CrForms r (m + 1) n) (hV : jet r (pull m i ω) ∈ CrForms r m n) :
    (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) :=
  viaRep_spec (fun _ _ h => pull_congr i h) hD hC hV

theorem faceCl_spec {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω)
    (hw : jet r ω ∈ CrClosed r (m + 1) n) (hV : jet r (pull m i ω) ∈ CrClosed r m n) :
    (faceCl r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) :=
  viaRep_spec (fun _ _ h => pull_congr i h) hD hC hV

theorem dCr_spec {n : ℕ} {ω : Ω m} (hD : IsDeg n ω) (hC : IsCr r ω)
    (hw : jet r ω ∈ CrForms r m n) (hV : jet r (extD ω) ∈ CrClosed r m (n + 1)) :
    (dCr r m n ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (extD ω) :=
  viaRep_spec (fun _ _ h => extD_congr h) hD hC hV

end Rep

section Pull

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

theorem pull_isDeg {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (h : IsDeg n ω) :
    IsDeg n (pull m i ω) := fun x hx =>
  map_mem_exteriorPower _ (h _ (coface_mem i hx))

theorem coeff_pull (i : Fin (m + 2)) (ω : Ω (m + 1)) (J : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (pull m i ω) J x = ∑ I, coeff ω I (coface m i x) *
      (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J := by
  simp only [coeff, pull]
  conv_lhs => rw [← (formBasis (m + 1)).sum_repr (ω (coface m i x))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem coface_eq_clm (i : Fin (m + 2)) : coface m i =
    fun x => vertex (m + 1) (i.succAbove 0) + LinearMap.toContinuousLinearMap (cofaceLin m i) x :=
  rfl

theorem hasFDerivAt_coface (i : Fin (m + 2)) (x : Fin m → ℝ) :
    HasFDerivAt (coface m i) (LinearMap.toContinuousLinearMap (cofaceLin m i)) x := by
  rw [coface_eq_clm]
  exact (LinearMap.toContinuousLinearMap (cofaceLin m i)).hasFDerivAt.const_add _

theorem contDiff_coface {n : WithTop ℕ∞} (i : Fin (m + 2)) : ContDiff ℝ n (coface m i) := by
  rw [coface_eq_clm]
  exact contDiff_const.add (ContinuousLinearMap.contDiff _)

theorem contDiffOn_coeff_pull (i : Fin (m + 2)) {ω : Ω (m + 1)}
    (h : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex (m + 1))) (J : Finset (Fin m)) :
    ContDiffOn ℝ r (coeff (pull m i ω) J) (simplex m) := by
  have e : coeff (pull m i ω) J = fun x => ∑ I, coeff ω I (coface m i x) *
      (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J :=
    funext (coeff_pull i ω J)
  rw [e]
  exact ContDiffOn.sum fun I _ =>
    ((h I).comp (contDiff_coface i).contDiffOn (fun x hx => coface_mem i hx)).mul contDiffOn_const

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

/-- The coefficients of the pulled-back basis forms. -/
noncomputable def pc (i : Fin (m + 2)) (I : Finset (Fin (m + 1))) (J : Finset (Fin m)) : ℝ :=
  (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J

theorem extD_pull (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)}
    (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex (m + 1))) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (pull m i ω) x = pull m i (extD ω) x := by
  have hy : coface m i x ∈ simplex (m + 1) := coface_mem i hx
  have hd : ∀ I, HasFDerivWithinAt (coeff ω I)
      (fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)) (simplex (m + 1))
      (coface m i x) := fun I =>
    (((hC I).differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) _ hy).hasFDerivWithinAt
  have hpd : ∀ J (k : Fin m), fderivWithin ℝ (coeff (pull m i ω) J) (simplex m) x (Pi.single k 1) =
      ∑ I, fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)
        (cofaceLin m i (Pi.single k 1)) * pc i I J := by
    intro J k
    have e : coeff (pull m i ω) J = fun x => ∑ I, coeff ω I (coface m i x) * pc i I J :=
      funext (coeff_pull i ω J)
    have hH : HasFDerivWithinAt (fun x => ∑ I, coeff ω I (coface m i x) * pc i I J)
        (∑ I, (pc i I J) • ((fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)).comp
          (LinearMap.toContinuousLinearMap (cofaceLin m i)))) (simplex m) x := by
      refine HasFDerivWithinAt.fun_sum (u := Finset.univ) fun I _ => ?_
      exact ((hd I).comp x (hasFDerivAt_coface i x).hasFDerivWithinAt
        (fun z hz => coface_mem i hz)).mul_const (pc i I J)
    rw [e, hH.fderivWithin (uniqueDiffOn_simplex m x hx)]
    simp [mul_comm]
  let T : (Fin (m + 1) → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin (m + 1) → ℝ)) :=
    ∑ I, ((fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x) :
      (Fin (m + 1) → ℝ) →L[ℝ] ℝ) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ).smulRight (formBasis (m + 1) I)
  have hT : ∀ v, T v = ∑ I, fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x) v •
      formBasis (m + 1) I := by
    intro v; simp [T]
  have hR : pull m i (extD ω) x = ExteriorAlgebra.map (cofaceLin m i).dualMap
      (∑ a, dx (m + 1) a * T (Pi.single a 1)) := by
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

theorem pull_isCr (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω) :
    IsCr r (pull m i ω) := fun J =>
  ⟨contDiffOn_coeff_pull i (fun I => (hC I).1) J,
    (contDiffOn_coeff_pull i (fun I => (hC I).2) J).congr fun x hx => by
      show (formBasis m).repr (extD (pull m i ω) x) J = (formBasis m).repr (pull m i (extD ω) x) J
      rw [extD_pull hr i (fun I => (hC I).1) hx]⟩

theorem pull_isClosedForm (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω)
    (h : IsClosedForm ω) : IsClosedForm (pull m i ω) := fun x hx => by
  rw [extD_pull hr i (fun I => (hC I).1) hx]
  show ExteriorAlgebra.map _ (extD ω (coface m i x)) = 0
  rw [h _ (coface_mem i hx), map_zero]

theorem faceCr_eq {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hw : jet r ω ∈ CrForms r (m + 1) n) :
    (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) := by
  refine faceCr_spec i hD hC hw ?_
  show jet r (pull m i ω) ∈ (CrForms r m n : Set (Jet r m × Jet r m))
  rw [crForms_eq_image hr n]
  exact ⟨_, ⟨pull_isDeg i hD, pull_isCr hr i hC⟩, rfl⟩

theorem faceCl_eq {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hcl : IsClosedForm ω) (hw : jet r ω ∈ CrClosed r (m + 1) n) :
    (faceCl r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) := by
  refine faceCl_spec i hD hC hw ?_
  show jet r (pull m i ω) ∈ (CrClosed r m n : Set (Jet r m × Jet r m))
  rw [crClosed_eq_image hr n]
  exact ⟨_, ⟨pull_isDeg i hD, pull_isCr hr i hC, pull_isClosedForm hr i hC hcl⟩, rfl⟩

end Pull

end IntLInfty.Kan.A83

open IntLInfty.Kan in
theorem solution :
    (∀ (m : ℕ), Convex ℝ (simplex m)) ∧
    (∀ (m : ℕ), UniqueDiffOn ℝ (simplex m)) ∧
    (∀ {m : ℕ} (ω ω' : Ω m) (I : Finset (Fin m)),
      coeff (ω + ω') I = coeff ω I + coeff ω' I) ∧
    (∀ {m : ℕ} (c : ℝ) (ω : Ω m) (I : Finset (Fin m)),
      coeff (c • ω) I = c • coeff ω I) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') {x : Fin m → ℝ}
      (hx : x ∈ simplex m), extD (ω + ω') x = extD ω x + extD ω' x) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) {x : Fin m → ℝ}
      (hx : x ∈ simplex m), extD (c • ω) x = c • extD ω x) ∧
    (∀ {m : ℕ} {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω'), IsDeg n (ω + ω')) ∧
    (∀ {m : ℕ} {n : ℕ} (c : ℝ) {ω : Ω m} (h : IsDeg n ω), IsDeg n (c • ω)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω'), IsCr r (ω + ω')) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω), IsCr r (c • ω)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω'),
      jet r (ω + ω') = jet r ω + jet r ω') ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω),
      jet r (c • ω) = c • jet r ω) ∧
    (∀ {m r : ℕ}, IsCr r (0 : Ω m)) ∧
    (∀ {m : ℕ} {n : ℕ}, IsDeg n (0 : Ω m)) ∧
    (∀ (m : ℕ), IsClosed (simplex m)) ∧
    (∀ {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
      (hk : k ≤ r) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m),
      jetComp f k β ⟨x, hx⟩ = iteratedFDerivWithin ℝ k f (simplex m) x (fun l => Pi.single (β l) 1)) ∧
    (∀ {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
      (hk : k = 0) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m),
      jetComp f k β ⟨x, hx⟩ = f x) ∧
    (∀ {r m : ℕ} (I : Finset (Fin m)) (j : Fin (r + 1))
      (β : Fin (j : ℕ) → Fin m), Continuous (fun w : Jet r m => w I j β)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω : Ω m} (hC : IsCr r ω), IsClosedForm (extD ω)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
      (h : IsClosedForm ω) (h' : IsClosedForm ω'), IsClosedForm (ω + ω')) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω)
      (h : IsClosedForm ω), IsClosedForm (c • ω)) ∧
    (∀ {m : ℕ}, IsClosedForm (0 : Ω m)) ∧
    (∀ {m : ℕ} {ω ω' : Ω m} (h : ∀ x ∈ simplex m, ω x = ω' x) (I : Finset (Fin m)),
      Set.EqOn (coeff ω I) (coeff ω' I) (simplex m)) ∧
    (∀ {m : ℕ} {ω ω' : Ω m} (h : ∀ x ∈ simplex m, ω x = ω' x),
      ∀ x ∈ simplex m, extD ω x = extD ω' x) ∧
    (∀ {m r : ℕ} {ω ω' : Ω m} (h : ∀ x ∈ simplex m, ω x = ω' x), jet r ω = jet r ω') ∧
    (∀ {m r : ℕ} {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
      (h : jet r ω = jet r ω'), ∀ x ∈ simplex m, ω x = ω' x) ∧
    (∀ (m : ℕ) (j : Fin (m + 1)), vertex m j ∈ simplex m) ∧
    (∀ {m : ℕ} (i : Fin (m + 2)) {x : Fin m → ℝ} (hx : x ∈ simplex m),
      coface m i x ∈ simplex (m + 1)) ∧
    (∀ {m r : ℕ} {m' n : ℕ} {V : Submodule ℝ (Jet r m' × Jet r m')} {F : Ω m → Ω m'}
      (hF : ∀ ω ω' : Ω m, (∀ x ∈ simplex m, ω x = ω' x) → ∀ x ∈ simplex m', F ω x = F ω' x)
      {ω : Ω m} (hD : IsDeg n ω) (hC : IsCr r ω) (hV : jet r (F ω) ∈ V),
      (viaRep n V F (jet r ω) : Jet r m' × Jet r m') = jet r (F ω)) ∧
    (∀ {m r : ℕ} {n : ℕ} {ω : Ω m} (hD : IsDeg n ω) (hC : IsCr r ω)
      (hw : jet r ω ∈ CrForms r m n) (hV : jet r (extD ω) ∈ CrClosed r m (n + 1)),
      (dCr r m n ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (extD ω)) ∧
    (∀ {M N : Type} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
      [Module ℝ N] (f : M →ₗ[ℝ] N) {n : ℕ} {a : ExteriorAlgebra ℝ M} (ha : a ∈ ⋀[ℝ]^n M),
      ExteriorAlgebra.map f a ∈ ⋀[ℝ]^n N) ∧
    (∀ {m : ℕ} {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (h : IsDeg n ω),
      IsDeg n (pull m i ω)) ∧
    (∀ {m' : ℕ} {A : Type} [AddCommGroup A] [Module ℝ A]
      (T : (Fin m' → ℝ) →ₗ[ℝ] A) (v : Fin m' → ℝ), T v = ∑ a, v a • T (Pi.single a 1)) ∧
    (∀ {m : ℕ} {m' : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ))
      (T : (Fin m' → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m' → ℝ))),
      ExteriorAlgebra.map L.dualMap (∑ a, dx m' a * T (Pi.single a 1)) =
        ∑ k, dx m k * ExteriorAlgebra.map L.dualMap (T (L (Pi.single k 1)))) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)}
      (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex (m + 1))) {x : Fin m → ℝ}
      (hx : x ∈ simplex m), extD (pull m i ω) x = pull m i (extD ω) x) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω),
      IsCr r (pull m i ω)) ∧
    (∀ {m r : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω)
      (h : IsClosedForm ω), IsClosedForm (pull m i ω)) ∧
    (∀ {m r : ℕ} {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
      (hC : IsCr r ω) (hw : jet r ω ∈ CrForms r (m + 1) n),
      (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω)) ∧
    (∀ {m r : ℕ} {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
      (hC : IsCr r ω) (hcl : IsClosedForm ω) (hw : jet r ω ∈ CrClosed r (m + 1) n),
      (faceCl r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω)) := by
  exact
      ⟨IntLInfty.Kan.A83.convex_simplex,
       IntLInfty.Kan.A83.uniqueDiffOn_simplex,
       IntLInfty.Kan.A83.coeff_add,
       IntLInfty.Kan.A83.coeff_smul,
       IntLInfty.Kan.A83.extD_add,
       IntLInfty.Kan.A83.extD_smul,
       IntLInfty.Kan.A83.isDeg_add,
       IntLInfty.Kan.A83.isDeg_smul,
       IntLInfty.Kan.A83.isCr_add,
       IntLInfty.Kan.A83.isCr_smul,
       IntLInfty.Kan.A83.jet_add,
       IntLInfty.Kan.A83.jet_smul,
       IntLInfty.Kan.A83.isCr_zero,
       IntLInfty.Kan.A83.isDeg_zero,
       IntLInfty.Kan.A83.isClosed_simplex,
       IntLInfty.Kan.A83.jetComp_apply,
       IntLInfty.Kan.A83.jetComp_zero,
       IntLInfty.Kan.A83.continuous_jet_eval,
       IntLInfty.Kan.A83.extD_extD,
       IntLInfty.Kan.A83.isClosedForm_add,
       IntLInfty.Kan.A83.isClosedForm_smul,
       IntLInfty.Kan.A83.isClosedForm_zero,
       IntLInfty.Kan.A83.coeff_eqOn,
       IntLInfty.Kan.A83.extD_congr,
       IntLInfty.Kan.A83.jet_congr,
       IntLInfty.Kan.A83.formEqOn_of_jet,
       IntLInfty.Kan.A83.vertex_mem,
       IntLInfty.Kan.A83.coface_mem,
       IntLInfty.Kan.A83.viaRep_spec,
       IntLInfty.Kan.A83.dCr_spec,
       IntLInfty.Kan.A83.map_mem_exteriorPower,
       IntLInfty.Kan.A83.pull_isDeg,
       IntLInfty.Kan.A83.linear_expand,
       IntLInfty.Kan.A83.wedge_natural,
       IntLInfty.Kan.A83.extD_pull,
       IntLInfty.Kan.A83.pull_isCr,
       IntLInfty.Kan.A83.pull_isClosedForm,
       IntLInfty.Kan.A83.faceCr_eq,
       IntLInfty.Kan.A83.faceCl_eq⟩
