-- Prove2me | solution 1 for IntLInfty.Kan.cone_homotopy_operator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:47:53.042205+00:00
-- url     : https://prove2.me/submissions/4af97e3e-c94a-4124-a300-e297ba4ca262

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

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
  have key : ∀ ψ : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ψ x • G x = 0 := by
    intro ψ hψ hψc hψU
    have hψ1 : ContDiff ℝ 1 ψ := contDiff_infty.1 hψ 1
    have hψ2 : ContDiff ℝ 2 ψ := contDiff_infty.1 hψ 2
    set D : Fin m → (Fin m → ℝ) → ℝ := fun l x => fderiv ℝ ψ x (e l) with hD
    have hD1 : ∀ l, ContDiff ℝ 1 (D l) := fun l =>
      (hψ2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hDc : ∀ l, HasCompactSupport (D l) := fun l => hψc.fderiv_apply ℝ (e l)
    have hDU : ∀ l, tsupport (D l) ⊆ U := fun l => (tsupport_fderiv_apply_subset ℝ (e l)).trans hψU
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

end JetClosed

theorem crForms_eq_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} := by
  rw [crForms_coe hr n, (jetImage_closed hr n).closure_eq]

section ClosedSpan

variable {m r : ℕ}

end ClosedSpan

section Rep

variable {m r : ℕ}

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

theorem faceCr_eq {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hw : jet r ω ∈ CrForms r (m + 1) n) :
    (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) := by
  refine faceCr_spec i hD hC hw ?_
  show jet r (pull m i ω) ∈ (CrForms r m n : Set (Jet r m × Jet r m))
  rw [crForms_eq_image hr n]
  exact ⟨_, ⟨pull_isDeg i hD, pull_isCr hr i hC⟩, rfl⟩

end Pull

section PullAff

variable {m m' r : ℕ}

end PullAff

section PullS

variable {m m' r : ℕ}

end PullS

section HornExt

variable {m r : ℕ}

end HornExt

section HornJet

variable {m r : ℕ}

end HornJet

section Fold

variable {m r : ℕ}

end Fold

section ClosedGraph

variable {m r : ℕ}

def CoeffTendsto (ωk : ℕ → Ω m) (ω : Ω m) : Prop :=
  ∀ I, ∀ x ∈ simplex m, Tendsto (fun k => coeff (ωk k) I x) atTop (𝓝 (coeff ω I x))

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

theorem coeffTendsto_unique {ωk : ℕ → Ω m} {a b : Ω m} (h1 : CoeffTendsto ωk a)
    (h2 : CoeffTendsto ωk b) : FormEqOn a b := fun x hx =>
  (formBasis m).ext_elem fun I => tendsto_nhds_unique (h1 I x hx) (h2 I x hx)

theorem exists_rep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    ∃ ω : Ω m, (IsDeg n ω ∧ IsCr r ω) ∧ jet r ω = w := by
  have := w.2
  rw [← SetLike.mem_coe, crForms_eq_image hr n] at this
  exact this

open BoundedContinuousFunction in
theorem jet_complete (r m : ℕ) : CompleteSpace (Jet r m × Jet r m) := by
  have : CompleteSpace (Jet r m) := inferInstanceAs (CompleteSpace ((I : Finset (Fin m)) →
    (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ)))
  infer_instance

theorem crForms_complete (r m n : ℕ) : CompleteSpace (CrForms r m n) := by
  haveI := jet_complete r m
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem faceCr_val (hr : 1 ≤ r) {n : ℕ} (i : Fin (m + 2)) (w : CrForms r (m + 1) n)
    {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω) (h : jet r ω = w) :
    (faceCr r m n i w : Jet r m × Jet r m) = jet r (pull m i ω) := by
  obtain ⟨w, hw⟩ := w
  simp only at h
  subst h
  exact faceCr_eq hr i hD hC hw

end ClosedGraph

section HornSection

variable {m r : ℕ}

end HornSection

section Lemma59

variable {m r : ℕ}

end Lemma59

section Lemma59Closed

variable {m r : ℕ}

end Lemma59Closed

end IntLInfty.Kan.A83

set_option autoImplicit false

namespace IntLInfty.Kan.A83Cone

open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def coneInt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) (f : E → F)
    (x : E) : F :=
  ∫ t in (0 : ℝ)..1, (t ^ p) • f (t • x)

theorem norm_pow_le_one {p : ℕ} {t : ℝ} (ht : t ∈ Set.uIoc (0 : ℝ) 1) : ‖t ^ p‖ ≤ 1 := by
  rw [Set.uIoc_of_le zero_le_one] at ht
  rw [norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
  exact pow_le_one₀ ht.1.le ht.2

theorem mem_Icc_of_uIoc {t : ℝ} (ht : t ∈ Set.uIoc (0 : ℝ) 1) : t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.uIoc_of_le zero_le_one] at ht
  exact ⟨ht.1.le, ht.2⟩

variable {S : Set E}

theorem intervalIntegrable_cone {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F} (hf : ContinuousOn f S) (p : ℕ)
    {x : E} (hx : x ∈ S) :
    IntervalIntegrable (fun t : ℝ => (t ^ p) • f (t • x)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  refine ContinuousOn.smul (continuousOn_pow p) (hf.comp ?_ ?_)
  · exact (continuous_id.smul continuous_const).continuousOn
  · intro t ht
    exact hconv.smul_mem_of_zero_mem h0 hx ht

theorem uc_ray {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (hS : IsCompact S)
    (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F} (hf : ContinuousOn f S) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖f (t • y) - f (t • x)‖ < ε := by
  have hu := hS.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy t ht => ?_⟩
  have htx := hconv.smul_mem_of_zero_mem h0 hx ht
  have hty := hconv.smul_mem_of_zero_mem h0 hy ht
  have hd : dist (t • y) (t • x) < δ := by
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := by gcongr; exact ht.2
      _ = ‖y - x‖ := one_mul _
      _ < δ := hxy
  have := h _ hty _ htx hd
  rwa [dist_eq_norm] at this

theorem continuousOn_coneInt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hS : IsCompact S) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F}
    (hf : ContinuousOn f S) (p : ℕ) : ContinuousOn (coneInt p f) S := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  obtain ⟨δ, hδ, h⟩ := uc_ray hS hconv h0 hf (half_pos hε)
  refine ⟨δ, hδ, fun y hy hyx => ?_⟩
  rw [dist_eq_norm] at hyx ⊢
  simp only [coneInt]
  rw [← intervalIntegral.integral_sub (intervalIntegrable_cone hconv h0 hf p hy)
    (intervalIntegrable_cone hconv h0 hf p hx)]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(t ^ p) • f (t • y) - (t ^ p) • f (t • x)‖ ≤ ε / 2 := by
    intro t ht
    rw [← smul_sub, norm_smul]
    calc ‖t ^ p‖ * ‖f (t • y) - f (t • x)‖ ≤ 1 * (ε / 2) := by
          gcongr
          · exact norm_pow_le_one ht
          · exact (h x hx y hy hyx t (mem_Icc_of_uIoc ht)).le
      _ = ε / 2 := one_mul _
  calc _ ≤ ε / 2 * |(1 : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ < ε := by simp; linarith

theorem hasFDerivWithinAt_coneInt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (hS : IsCompact S) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F}
    {f' : E → E →L[ℝ] F} (hf : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x)
    (hf' : ContinuousOn f' S) (p : ℕ) {x : E} (hx : x ∈ S) :
    HasFDerivWithinAt (coneInt p f) (coneInt (p + 1) f' x) S x := by
  have hfc : ContinuousOn f S := fun y hy => (hf y hy).continuousWithinAt
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hu := hS.uniformContinuousOn_of_continuous hf'
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu c hc
  have hball : ∀ᶠ y in 𝓝[S] x, y ∈ S ∧ ‖y - x‖ < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)]
      with y hy hb
    exact ⟨hy, by rwa [Metric.mem_ball, dist_eq_norm] at hb⟩
  filter_upwards [hball] with y hyy
  obtain ⟨hy, hyx⟩ := hyy
  have hI1 := intervalIntegrable_cone hconv h0 hfc p hy
  have hI2 := intervalIntegrable_cone hconv h0 hfc p hx
  have hI3 := intervalIntegrable_cone hconv h0 hf' (p + 1) hx
  have hray : ContinuousOn (fun t : ℝ => f' (t • x)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    refine hf'.comp (continuous_id.smul continuous_const).continuousOn ?_
    intro t ht
    exact hconv.smul_mem_of_zero_mem h0 hx ht
  have hI4 : IntervalIntegrable (fun t : ℝ => (t ^ p) • (f' (t • x)) (t • y - t • x))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.smul (continuousOn_pow p) (hray.clm_apply ?_)
    exact ((continuous_id.smul continuous_const).sub
      (continuous_id.smul continuous_const)).continuousOn
  have happ : (coneInt (p + 1) f' x) (y - x) =
      ∫ t in (0 : ℝ)..1, (t ^ p) • (f' (t • x)) (t • y - t • x) := by
    simp only [coneInt]
    rw [ContinuousLinearMap.intervalIntegral_apply hI3]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [FunLike.coe_smul, Pi.smul_apply, ← smul_sub, map_smul, smul_smul, pow_succ]
  have hsplit : coneInt p f y - coneInt p f x - (coneInt (p + 1) f' x) (y - x) =
      ∫ t in (0 : ℝ)..1, (t ^ p) • (f (t • y) - f (t • x) - (f' (t • x)) (t • y - t • x)) := by
    rw [happ]
    simp only [coneInt]
    rw [← intervalIntegral.integral_sub hI1 hI2, ← intervalIntegral.integral_sub (hI1.sub hI2) hI4]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [smul_sub]
  rw [hsplit]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(t ^ p) • (f (t • y) - f (t • x) - (f' (t • x)) (t • y - t • x))‖ ≤ c * ‖y - x‖ := by
    intro t ht
    have ht' := mem_Icc_of_uIoc ht
    have htx := hconv.smul_mem_of_zero_mem h0 hx ht'
    have hty := hconv.smul_mem_of_zero_mem h0 hy ht'
    have hseg : segment ℝ (t • x) (t • y) ⊆ S := hconv.segment_subset htx hty
    have hle : ‖t • y - t • x‖ ≤ ‖y - x‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := by gcongr; exact ht'.2
        _ = ‖y - x‖ := one_mul _
    have hmv : ‖f (t • y) - f (t • x) - (f' (t • x)) (t • y - t • x)‖ ≤ c * ‖t • y - t • x‖ := by
      refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun z hz => (hf z (hseg hz)).mono hseg) (fun z hz => ?_) (convex_segment _ _)
        (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
      have hzb : z ∈ Metric.closedBall (t • x) ‖t • y - t • x‖ :=
        (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self (norm_nonneg _))
          (by rw [Metric.mem_closedBall, dist_eq_norm]) hz
      rw [Metric.mem_closedBall] at hzb
      have := h z (hseg hz) (t • x) htx (lt_of_le_of_lt (hzb.trans hle) hyx)
      rw [dist_eq_norm] at this
      exact this.le
    rw [norm_smul]
    calc ‖t ^ p‖ * ‖f (t • y) - f (t • x) - (f' (t • x)) (t • y - t • x)‖
        ≤ 1 * (c * ‖y - x‖) := by
          gcongr
          · exact norm_pow_le_one ht
          · exact hmv.trans (by gcongr)
      _ = c * ‖y - x‖ := one_mul _
  calc _ ≤ c * ‖y - x‖ * |(1 : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = c * ‖y - x‖ := by simp

theorem contDiffOn_coneInt (hS : IsCompact S) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S)
    (hU : UniqueDiffOn ℝ S) (r : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E → F)
      (p : ℕ), ContDiffOn ℝ r f S → ContDiffOn ℝ r (coneInt p f) S := by
  induction r with
  | zero =>
    intro F _ _ _ f p hf
    rw [Nat.cast_zero, contDiffOn_zero] at hf ⊢
    exact continuousOn_coneInt hS hconv h0 hf p
  | succ r ih =>
    intro F _ _ _ f p hf
    have hd : ∀ x ∈ S, HasFDerivWithinAt f (fderivWithin ℝ f S x) S x := fun x hx =>
      ((hf.differentiableOn (by simp)) x hx).hasFDerivWithinAt
    have hc : ContinuousOn (fderivWithin ℝ f S) S := hf.continuousOn_fderivWithin hU (by simp)
    have hD := fun (x : E) (hx : x ∈ S) => hasFDerivWithinAt_coneInt hS hconv h0 hd hc p hx
    have hfd : ContDiffOn ℝ r (fderivWithin ℝ f S) S := hf.fderivWithin hU (by push_cast; rfl)
    rw [show ((r + 1 : ℕ) : WithTop ℕ∞) = (r : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderivWithin hU]
    refine ⟨fun x hx => (hD x hx).differentiableWithinAt, by simp, ?_⟩
    exact (ih (fderivWithin ℝ f S) (p + 1) hfd).congr fun x hx => (hD x hx).fderivWithin (hU x hx)

theorem cone_euler {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F} {f' : E → E →L[ℝ] F}
    (hf : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x) (hf' : ContinuousOn f' S) (p : ℕ) {x : E}
    (hx : x ∈ S) :
    ((p : ℝ) + 1) • coneInt p f x + (coneInt (p + 1) f' x) x = f x := by
  have hfc : ContinuousOn f S := fun y hy => (hf y hy).continuousWithinAt
  have hmaps : Set.MapsTo (fun s : ℝ => s • x) (Set.Icc 0 1) S := fun t ht =>
    hconv.smul_mem_of_zero_mem h0 hx ht
  have hI1 := intervalIntegrable_cone hconv h0 hfc p hx
  have hI3 := intervalIntegrable_cone hconv h0 hf' (p + 1) hx
  have hray : ContinuousOn (fun t : ℝ => f' (t • x)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact hf'.comp (continuous_id.smul continuous_const).continuousOn hmaps
  have hrayf : ContinuousOn (fun t : ℝ => f (t • x)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact hfc.comp (continuous_id.smul continuous_const).continuousOn hmaps
  have hA : IntervalIntegrable (fun t : ℝ => t ^ (p + 1) • (f' (t • x)) x)
      MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable ((continuousOn_pow _).smul (hray.clm_apply continuousOn_const))
  have hB : IntervalIntegrable (fun t : ℝ => (((p : ℝ) + 1) * t ^ p) • f (t • x))
      MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable
      ((continuousOn_const.mul (continuousOn_pow p)).smul hrayf)
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => s ^ (p + 1) • f (s • x))
      (t ^ (p + 1) • (f' (t • x)) x + (((p : ℝ) + 1) * t ^ p) • f (t • x)) (Set.Icc 0 1) t := by
    intro t ht
    have hin : HasDerivWithinAt (fun s : ℝ => s • x) x (Set.Icc 0 1) t := by
      simpa using ((hasDerivAt_id t).smul_const x).hasDerivWithinAt
    have hcomp : HasDerivWithinAt (fun s : ℝ => f (s • x)) ((f' (t • x)) x) (Set.Icc 0 1) t :=
      (hf _ (hmaps ht)).comp_hasDerivWithinAt t hin hmaps
    have hpow : HasDerivWithinAt (fun s : ℝ => s ^ (p + 1)) (((p : ℝ) + 1) * t ^ p)
        (Set.Icc 0 1) t := by
      simpa using (hasDerivAt_pow (p + 1) t).hasDerivWithinAt
    exact hpow.smul hcomp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (f := fun s : ℝ => s ^ (p + 1) • f (s • x))
    (f' := fun t => t ^ (p + 1) • (f' (t • x)) x + (((p : ℝ) + 1) * t ^ p) • f (t • x))
    (fun t ht => (hderiv t ht).continuousWithinAt)
    (fun t ht => (hderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))
    (hA.add hB)
  simp only [one_pow, one_smul, zero_pow (Nat.succ_ne_zero p), zero_smul, sub_zero] at hFTC
  have e1 : (coneInt (p + 1) f' x) x = ∫ t in (0 : ℝ)..1, t ^ (p + 1) • (f' (t • x)) x := by
    simp only [coneInt]
    rw [ContinuousLinearMap.intervalIntegral_apply hI3]
    exact intervalIntegral.integral_congr fun t _ => by simp
  have e2 : ((p : ℝ) + 1) • coneInt p f x =
      ∫ t in (0 : ℝ)..1, (((p : ℝ) + 1) * t ^ p) • f (t • x) := by
    simp only [coneInt]
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr fun t _ => by simp [mul_smul]
  rw [e1, e2, ← hFTC, intervalIntegral.integral_add hA hB, add_comm]

end IntLInfty.Kan.A83Cone

namespace IntLInfty.Kan.A83Poinc

open IntLInfty.Kan IntLInfty.Kan.A83Cone

abbrev Alg (m : ℕ) : Type := ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))

@[reducible] noncomputable def algNAG (m : ℕ) : NormedAddCommGroup (Alg m) :=
  NormedAddCommGroup.induced (Alg m) (Finset (Fin m) → ℝ) (formBasis m).equivFun.toLinearMap
    (formBasis m).equivFun.injective

attribute [local instance] algNAG

@[reducible] noncomputable def algNS (m : ℕ) : NormedSpace ℝ (Alg m) :=
  NormedSpace.induced ℝ (Alg m) (Finset (Fin m) → ℝ) (formBasis m).equivFun.toLinearMap

attribute [local instance] algNS

theorem algFD (m : ℕ) : FiniteDimensional ℝ (Alg m) := Module.Finite.of_basis (formBasis m)

attribute [local instance] algFD

theorem algComplete (m : ℕ) : CompleteSpace (Alg m) := FiniteDimensional.complete ℝ (Alg m)

attribute [local instance] algComplete

theorem single_eq_smul {m : ℕ} (y : Fin m → ℝ) (k : Fin m) :
    (Pi.single k (y k) : Fin m → ℝ) = y k • (Pi.single k (1 : ℝ) : Fin m → ℝ) := by
  ext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem sum_single_smul {m : ℕ} (y : Fin m → ℝ) :
    ∑ k : Fin m, y k • (Pi.single k (1 : ℝ) : Fin m → ℝ) = y := by
  conv_rhs => rw [← Finset.univ_sum_single y]
  exact Finset.sum_congr rfl fun k _ => (single_eq_smul y k).symm

theorem sum_proj (m : ℕ) (φ : Module.Dual ℝ (Fin m → ℝ)) :
    ∑ k : Fin m, φ (Pi.single k 1) • (LinearMap.proj k : (Fin m → ℝ) →ₗ[ℝ] ℝ) = φ := by
  apply LinearMap.ext
  intro y
  rw [LinearMap.sum_apply]
  conv_rhs => rw [← sum_single_smul y, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, LinearMap.proj_apply, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

noncomputable def numOp (m : ℕ) : Alg m →ₗ[ℝ] Alg m :=
  ∑ k : Fin m, (LinearMap.mulLeft ℝ (dx m k)) ∘ₗ
    CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) (Pi.single k 1))

theorem numOp_apply (m : ℕ) (a : Alg m) :
    numOp m a = ∑ k : Fin m, dx m k *
      CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) (Pi.single k 1)) a := by
  simp [numOp, LinearMap.sum_apply]

theorem contract_dx_mul (m : ℕ) (x : Fin m → ℝ) (k : Fin m) (b : Alg m) :
    CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) x) (dx m k * b)
      = x k • b - dx m k * CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) x) b := by
  unfold dx
  rw [CliffordAlgebra.contractLeft_ι_mul]
  rfl

theorem numOp_iota_mul (m : ℕ) (φ : Module.Dual ℝ (Fin m → ℝ)) (x : Alg m) :
    numOp m (ExteriorAlgebra.ι ℝ φ * x) = ExteriorAlgebra.ι ℝ φ * x + ExteriorAlgebra.ι ℝ φ * numOp m x := by
  have h1 : ∀ k : Fin m, dx m k * CliffordAlgebra.contractLeft
      (Module.Dual.eval ℝ (Fin m → ℝ) (Pi.single k 1)) (ExteriorAlgebra.ι ℝ φ * x)
      = φ (Pi.single k 1) • (dx m k * x) + ExteriorAlgebra.ι ℝ φ * (dx m k *
        CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) (Pi.single k 1)) x) := by
    intro k
    have hswap : dx m k * ExteriorAlgebra.ι ℝ φ = -(ExteriorAlgebra.ι ℝ φ * dx m k) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    rw [CliffordAlgebra.contractLeft_ι_mul, Module.Dual.eval_apply, mul_sub, mul_smul_comm,
      ← mul_assoc, hswap, neg_mul, sub_neg_eq_add, mul_assoc]
  have h2 : ∑ k : Fin m, φ (Pi.single k 1) • (dx m k * x) = ExteriorAlgebra.ι ℝ φ * x := by
    simp_rw [← smul_mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    unfold dx
    simp_rw [← map_smul]
    rw [← map_sum, sum_proj]
  rw [numOp_apply, Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_add_distrib, h2, numOp_apply,
    Finset.mul_sum]

theorem numOp_pow (m n : ℕ) (a : Alg m) (ha : a ∈ ⋀[ℝ]^n (Module.Dual ℝ (Fin m → ℝ))) :
    numOp m a = (n : ℝ) • a := by
  have ha' : a ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : Module.Dual ℝ (Fin m → ℝ) →ₗ[ℝ] Alg m) ^ n :=
    ha
  clear ha
  induction ha' using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [numOp_apply]
    simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y i _ _ hx hy =>
    rw [map_add, hx, hy, smul_add]
  | mem_mul m' hm i x _ ih =>
    obtain ⟨φ, rfl⟩ := hm
    rw [numOp_iota_mul, ih, mul_smul_comm, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      add_smul, one_smul, add_comm]

noncomputable def cL (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] Alg m →ₗ[ℝ] Alg m :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))).comp
    (Module.Dual.eval ℝ (Fin m → ℝ))

noncomputable def cB (m : ℕ) : (Fin m → ℝ) →L[ℝ] Alg m →L[ℝ] Alg m :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Alg m →ₗ[ℝ] Alg m) ≃ₗ[ℝ] (Alg m →L[ℝ] Alg m)).toLinearMap
      ∘ₗ cL m)

theorem cB_apply (m : ℕ) (x : Fin m → ℝ) (a : Alg m) :
    cB m x a = CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) x) a := rfl

noncomputable def L2 (m : ℕ) : ((Fin m → ℝ) →L[ℝ] Alg m) →L[ℝ] Alg m :=
  ∑ k : Fin m, (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (dx m k))).comp
    (ContinuousLinearMap.apply ℝ (Alg m) (Pi.single k 1))

theorem L2_apply (m : ℕ) (φ : (Fin m → ℝ) →L[ℝ] Alg m) :
    L2 m φ = ∑ k : Fin m, dx m k * φ (Pi.single k 1) := by
  simp [L2]

section generic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

theorem clm_coneInt_eq_zero {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : F →L[ℝ] G) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F} (hf : ContinuousOn f S)
    (hz : ∀ y ∈ S, L (f y) = 0) (p : ℕ) {x : E} (hx : x ∈ S) : L (coneInt p f x) = 0 := by
  unfold coneInt
  rw [← L.intervalIntegral_comp_comm (intervalIntegrable_cone hconv h0 hf p hx)]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : G))]
  · simp
  · intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only
    rw [map_smul, hz _ (hconv.smul_mem_of_zero_mem h0 hx ht), smul_zero]

end generic

theorem clm_apply_sum {m : ℕ} {F : Type} [AddCommGroup F] [Module ℝ F]
    (B : (Fin m → ℝ) →ₗ[ℝ] F) (x : Fin m → ℝ) :
    B x = ∑ k : Fin m, x k • B (Pi.single k 1) := by
  conv_lhs => rw [← sum_single_smul x]
  simp [map_sum, map_smul]

theorem poincare_gen {m n : ℕ} {S : Set (Fin m → ℝ)} (hS : IsCompact S) (hconv : Convex ℝ S)
    (h0 : (0 : Fin m → ℝ) ∈ S) (hU : UniqueDiffOn ℝ S) {β : (Fin m → ℝ) → Alg m}
    {β' : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] Alg m}
    (hβ : ∀ y ∈ S, HasFDerivWithinAt β (β' y) S y) (hβ' : ContinuousOn β' S)
    (hdeg : ∀ y ∈ S, β y ∈ ⋀[ℝ]^(n + 1) (Module.Dual ℝ (Fin m → ℝ)))
    {x : Fin m → ℝ} (hx : x ∈ S) :
    ∑ k : Fin m, dx m k *
      fderivWithin ℝ (fun y => cB m y (coneInt n β y)) S x (Pi.single k 1)
      + cB m x (coneInt (n + 1) (fun y => L2 m (β' y)) x) = β x := by
  have hβc : ContinuousOn β S := fun y hy => (hβ y hy).continuousWithinAt
  have hg := hasFDerivWithinAt_coneInt hS hconv h0 hβ hβ' n hx
  have hK : HasFDerivWithinAt (fun y => cB m y (coneInt n β y)) _ S x :=
    (cB m).hasFDerivWithinAt_of_bilinear (hasFDerivWithinAt_id x S) hg
  have hD : ∀ v, fderivWithin ℝ (fun y => cB m y (coneInt n β y)) S x v
      = cB m x (coneInt (n + 1) β' x v) + cB m v (coneInt n β x) := by
    intro v
    rw [hK.fderivWithin (hU x hx)]
    simp
  simp_rw [hD, mul_add, Finset.sum_add_distrib]
  have hnum : numOp m (coneInt n β x) = ((n : ℝ) + 1) • coneInt n β x := by
    have hz := clm_coneInt_eq_zero
      (LinearMap.toContinuousLinearMap (numOp m - ((n : ℝ) + 1) • LinearMap.id)) hconv h0 hβc
      (fun y hy => by
        have := numOp_pow m (n + 1) (β y) (hdeg y hy)
        simp [this]) n hx
    have hz' : numOp m (coneInt n β x) - ((n : ℝ) + 1) • coneInt n β x = 0 := by
      simpa using hz
    exact sub_eq_zero.mp hz'
  have h2 : ∑ k : Fin m, dx m k * cB m (Pi.single k 1) (coneInt n β x)
      = ((n : ℝ) + 1) • coneInt n β x := by
    rw [← hnum, numOp_apply]
    rfl
  have hL2 : L2 m (coneInt (n + 1) β' x) = coneInt (n + 1) (fun y => L2 m (β' y)) x := by
    unfold coneInt
    rw [← (L2 m).intervalIntegral_comp_comm (intervalIntegrable_cone hconv h0 hβ' (n + 1) hx)]
    simp only [map_smul]
  have h1 : ∑ k : Fin m, dx m k * cB m x (coneInt (n + 1) β' x (Pi.single k 1))
      = coneInt (n + 1) β' x x - cB m x (L2 m (coneInt (n + 1) β' x)) := by
    have e : ∀ k : Fin m, dx m k * cB m x (coneInt (n + 1) β' x (Pi.single k 1))
        = x k • coneInt (n + 1) β' x (Pi.single k 1)
          - cB m x (dx m k * coneInt (n + 1) β' x (Pi.single k 1)) := by
      intro k
      rw [cB_apply, cB_apply, contract_dx_mul]
      abel
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_sub_distrib, ← map_sum, ← L2_apply]
    congr 1
    exact (clm_apply_sum (coneInt (n + 1) β' x).toLinearMap x).symm
  rw [h1, h2, hL2]
  have := cone_euler hconv h0 hβ hβ' n hx
  rw [← this]
  abel

theorem isCompact_simplex (m : ℕ) : IsCompact (simplex m) :=
  Metric.isCompact_of_isClosed_isBounded (A83.isClosed_simplex m)
    ((Metric.isBounded_Icc (0 : Fin m → ℝ) 1).subset fun x hx =>
      ⟨fun i => hx.1 i, fun i =>
        (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2⟩)

theorem zero_mem_simplex (m : ℕ) : (0 : Fin m → ℝ) ∈ simplex m :=
  ⟨fun _ => le_refl 0, by simp⟩

noncomputable def coeffL (m : ℕ) (I : Finset (Fin m)) : Alg m →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.proj I).comp (formBasis m).equivFun.toLinearMap)

theorem coeffL_apply (m : ℕ) (I : Finset (Fin m)) (a : Alg m) :
    coeffL m I a = (formBasis m).repr a I := by
  simp [coeffL]

theorem coeff_eq_coeffL {m : ℕ} (ω : Ω m) (I : Finset (Fin m)) :
    coeff ω I = fun y => coeffL m I (ω y) := by
  funext y
  rw [coeffL_apply]
  rfl

theorem extD_eq_fderiv {m : ℕ} {ω : Ω m} {x : Fin m → ℝ} (hx : x ∈ simplex m)
    (hd : DifferentiableWithinAt ℝ ω (simplex m) x) :
    extD ω x = ∑ k : Fin m, dx m k * fderivWithin ℝ ω (simplex m) x (Pi.single k 1) := by
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hcomp : ∀ I, fderivWithin ℝ (coeff ω I) (simplex m) x
      = (coeffL m I).comp (fderivWithin ℝ ω (simplex m) x) := by
    intro I
    rw [coeff_eq_coeffL]
    exact ((coeffL m I).hasFDerivAt.comp_hasFDerivWithinAt x hd.hasFDerivWithinAt).fderivWithin
      (A83.uniqueDiffOn_simplex m x hx)
  simp_rw [hcomp, ContinuousLinearMap.comp_apply, coeffL_apply]
  exact (formBasis m).sum_repr _

theorem contDiffOn_of_coeff {m r : ℕ} {ω : Ω m} {S : Set (Fin m → ℝ)}
    (h : ∀ I, ContDiffOn ℝ r (coeff ω I) S) : ContDiffOn ℝ r ω S := by
  have e : ω = fun y => (formBasis m).equivFun.symm (fun I => coeff ω I y) := by
    funext y
    apply (formBasis m).equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext I
    simp [coeff]
  rw [e]
  exact (LinearMap.toContinuousLinearMap (formBasis m).equivFun.symm.toLinearMap).contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr h)

theorem coneInt_mem_alg {m p : ℕ} {S : Set (Fin m → ℝ)} (V : Submodule ℝ (Alg m))
    (hconv : Convex ℝ S) (h0 : (0 : Fin m → ℝ) ∈ S) {f : (Fin m → ℝ) → Alg m}
    (hf : ContinuousOn f S) (hfV : ∀ y ∈ S, f y ∈ V) {x : Fin m → ℝ} (hx : x ∈ S) :
    coneInt p f x ∈ V := by
  by_contra hnot
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  apply hφ
  have hz := clm_coneInt_eq_zero (LinearMap.toContinuousLinearMap φ) hconv h0 hf (fun y hy => by
    have hm : φ (f y) ∈ V.map φ := Submodule.mem_map_of_mem (hfV y hy)
    rw [hmap, Submodule.mem_bot] at hm
    simpa using hm) p hx
  simpa using hz

theorem contract_mem (m : ℕ) (d : Module.Dual ℝ (Module.Dual ℝ (Fin m → ℝ))) (i : ℕ) (a : Alg m)
    (ha : a ∈ ⋀[ℝ]^i (Module.Dual ℝ (Fin m → ℝ))) :
    CliffordAlgebra.contractLeft d a ∈ ⋀[ℝ]^(i - 1) (Module.Dual ℝ (Fin m → ℝ)) ∧
      (i = 0 → CliffordAlgebra.contractLeft d a = 0) := by
  have ha' : a ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : Module.Dual ℝ (Fin m → ℝ) →ₗ[ℝ] Alg m) ^ i :=
    ha
  clear ha
  induction ha' using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [CliffordAlgebra.contractLeft_algebraMap]
    exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
  | add x y i _ _ hx hy =>
    rw [map_add]
    exact ⟨Submodule.add_mem _ hx.1 hy.1, fun h => by rw [hx.2 h, hy.2 h, add_zero]⟩
  | mem_mul m' hm i x hxi ih =>
    obtain ⟨φ, rfl⟩ := hm
    refine ⟨?_, fun h => absurd h (Nat.succ_ne_zero i)⟩
    rw [CliffordAlgebra.contractLeft_ι_mul, Nat.succ_sub_one]
    refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hxi) ?_
    rcases i with _ | j
    · rw [ih.2 rfl, mul_zero]
      exact Submodule.zero_mem _
    · have h1 := ih.1
      rw [Nat.add_sub_cancel] at h1
      show _ ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : Module.Dual ℝ (Fin m → ℝ) →ₗ[ℝ] Alg m) ^ (j + 1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ φ) h1

noncomputable def Kop {m : ℕ} (n : ℕ) (β : Ω m) : Ω m := fun y => cB m y (coneInt n β y)

theorem Kop_hom {m n r : ℕ} (hr : 1 ≤ r) {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    ∀ x ∈ simplex m, extD (Kop n β) x + Kop (n + 1) (extD β) x = β x := by
  have hS := isCompact_simplex m
  have hconv := A83.convex_simplex m
  have h0 := zero_mem_simplex m
  have hU := A83.uniqueDiffOn_simplex m
  have hβC : ContDiffOn ℝ r β (simplex m) := contDiffOn_of_coeff fun I => (hC I).1
  have hr' : (1 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hr
  have hrne : (r : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hr)
  have hβd : ∀ y ∈ simplex m,
      HasFDerivWithinAt β (fderivWithin ℝ β (simplex m) y) (simplex m) y := fun y hy =>
    ((hβC.differentiableOn hrne) y hy).hasFDerivWithinAt
  have hβ' : ContinuousOn (fderivWithin ℝ β (simplex m)) (simplex m) :=
    hβC.continuousOn_fderivWithin hU hr'
  have hKC : ContDiffOn ℝ r (Kop n β) (simplex m) :=
    ContDiffOn.clm_apply ((cB m).contDiff.contDiffOn)
      (contDiffOn_coneInt hS hconv h0 hU r β n hβC)
  intro x hx
  have hcong : coneInt (n + 1) (extD β) x
      = coneInt (n + 1) (fun y => L2 m (fderivWithin ℝ β (simplex m) y)) x := by
    unfold coneInt
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hy : t • x ∈ simplex m := hconv.smul_mem_of_zero_mem h0 hx ht
    simp only
    rw [extD_eq_fderiv hy (hβd _ hy).differentiableWithinAt, L2_apply]
  rw [extD_eq_fderiv hx ((hKC.differentiableOn hrne) x hx)]
  show _ + cB m x (coneInt (n + 1) (extD β) x) = _
  rw [hcong]
  exact poincare_gen hS hconv h0 hU hβd hβ' hD hx

theorem fderivWithin_mem_of_mapsTo {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {p : Submodule ℝ E} {f : (Fin m → ℝ) → E} {s : Set (Fin m → ℝ)}
    {x : Fin m → ℝ} (hx : x ∈ s) (hs : UniqueDiffOn ℝ s) (hf : DifferentiableWithinAt ℝ f s x)
    (hp : ∀ y ∈ s, f y ∈ p) (v : Fin m → ℝ) : fderivWithin ℝ f s x v ∈ p := by
  by_contra hv
  obtain ⟨φ, hφv, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  let φ' : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap φ
  have h1 : fderivWithin ℝ (fun y => φ' (f y)) s x = φ'.comp (fderivWithin ℝ f s x) :=
    (φ'.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin (hs x hx)
  have h0 : ∀ y ∈ s, φ' (f y) = 0 := fun y hy => by
    have h : φ (f y) ∈ p.map φ := Submodule.mem_map_of_mem (hp y hy)
    rw [hφp] at h
    simpa [φ'] using h
  have h2 : fderivWithin ℝ (fun y => φ' (f y)) s x = 0 := by
    rw [fderivWithin_congr (f := fun _ => (0 : ℝ)) (fun y hy => h0 y hy) (h0 x hx)]
    simp
  apply hφv
  have h3 := congrArg (fun L : (Fin m → ℝ) →L[ℝ] ℝ => L v) (h1.symm.trans h2)
  simpa [φ'] using h3

theorem isDeg_extD {m n r : ℕ} (hr : 1 ≤ r) {ω : Ω m} (hC : IsCr r ω) (hD : IsDeg n ω) :
    IsDeg (n + 1) (extD ω) := by
  intro x hx
  have hd : DifferentiableWithinAt ℝ ω (simplex m) x :=
    ((contDiffOn_of_coeff fun I => (hC I).1).differentiableOn
      (by exact_mod_cast (show r ≠ 0 by omega))) x hx
  rw [extD_eq_fderiv hx hd]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hv := fderivWithin_mem_of_mapsTo hx (A83.uniqueDiffOn_simplex m) hd hD (Pi.single k 1)
  show _ ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : Module.Dual ℝ (Fin m → ℝ) →ₗ[ℝ] _) ^ (n + 1)
  rw [pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) hv

theorem isCr_extD {m r : ℕ} (hr : 1 ≤ r) {ω : Ω m} (hC : IsCr r ω) : IsCr r (extD ω) := by
  intro I
  refine ⟨(hC I).2, (contDiffOn_const (c := (0 : ℝ))).congr fun y hy => ?_⟩
  have h := A83.extD_extD hr hC y hy
  simp [coeff, h]

end IntLInfty.Kan.A83Poinc

namespace IntLInfty.Kan.A83Fill

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc

variable {m r : ℕ}

end IntLInfty.Kan.A83Fill

namespace IntLInfty.Kan.A83Graph

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end IntLInfty.Kan.A83Graph

namespace IntLInfty.Kan.A83Graph

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end IntLInfty.Kan.A83Graph

namespace IntLInfty.Kan.A83Proj

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem continuousOn_of_isCr {β : Ω m} (hC : IsCr r β) : ContinuousOn β (simplex m) :=
  (contDiffOn_of_coeff fun I => (hC I).1).continuousOn

theorem smul_mem_simplex {y : Fin m → ℝ} (hy : y ∈ simplex m) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • y ∈ simplex m :=
  (A83.convex_simplex m).smul_mem_of_zero_mem (zero_mem_simplex m) hy ht

theorem Kop_congr (n : ℕ) {β β' : Ω m} (h : FormEqOn β β') :
    FormEqOn (Kop n β) (Kop n β') := by
  intro y hy
  simp only [Kop, coneInt]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only [h _ (smul_mem_simplex hy ht)]

theorem coneInt_add' (n : ℕ) {β β' : Ω m} (hβ : ContinuousOn β (simplex m))
    (hβ' : ContinuousOn β' (simplex m)) {y : Fin m → ℝ} (hy : y ∈ simplex m) :
    coneInt n (β + β') y = coneInt n β y + coneInt n β' y := by
  simp only [coneInt, Pi.add_apply, smul_add]
  exact intervalIntegral.integral_add
    (intervalIntegrable_cone (A83.convex_simplex m) (zero_mem_simplex m) hβ n hy)
    (intervalIntegrable_cone (A83.convex_simplex m) (zero_mem_simplex m) hβ' n hy)

theorem coneInt_smul' (n : ℕ) (c : ℝ) (β : Ω m) (y : Fin m → ℝ) :
    coneInt n (c • β) y = c • coneInt n β y := by
  simp only [coneInt, Pi.smul_apply]
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext t
  rw [smul_comm]

theorem Kop_add (n : ℕ) {β β' : Ω m} (hβ : ContinuousOn β (simplex m))
    (hβ' : ContinuousOn β' (simplex m)) : FormEqOn (Kop n (β + β')) (Kop n β + Kop n β') := by
  intro y hy
  simp only [Kop, Pi.add_apply, coneInt_add' n hβ hβ' hy, map_add]

theorem Kop_smul (n : ℕ) (c : ℝ) (β : Ω m) : FormEqOn (Kop n (c • β)) (c • Kop n β) := by
  intro y _
  simp only [Kop, Pi.smul_apply, coneInt_smul', map_smul]

theorem Kop_sub (n : ℕ) {β β' : Ω m} (hβ : ContinuousOn β (simplex m))
    (hβ' : ContinuousOn β' (simplex m)) : FormEqOn (Kop n (β - β')) (Kop n β - Kop n β') := by
  intro y hy
  have e : β - β' = β + (-1 : ℝ) • β' := by funext z; simp [sub_eq_add_neg]
  have hc : ContinuousOn ((-1 : ℝ) • β') (simplex m) := hβ'.const_smul (-1 : ℝ)
  rw [e, Kop_add n hβ hc y hy, Pi.add_apply, Kop_smul n (-1) β' y hy]
  simp [sub_eq_add_neg]

theorem jet_zero' (hr : 1 ≤ r) : jet r (0 : Ω m) = 0 := by
  have := jet_smul hr (0 : ℝ) (isCr_zero (r := r) (m := m))
  simpa using this

end IntLInfty.Kan.A83Proj

namespace IntLInfty.Kan.A83Leib

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc

attribute [local instance] algNAG algNS algFD algComplete

variable {m : ℕ}

end IntLInfty.Kan.A83Leib

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan

section Ext

variable {V : Type} [AddCommGroup V] [Module ℝ V]

end Ext

section Lift

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end Lift

end IntLInfty.Kan.A83DGA

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83Proj

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83DGA

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83DGA

namespace IntLInfty.Kan.A83Tau

open IntLInfty.Kan IntLInfty.Kan.A83

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83Tau

namespace IntLInfty.Kan.A83Det

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

section Lift

variable {A : Type} [Ring A] [Algebra ℝ A]

end Lift

section OddTop

end OddTop

section EvenTop

end EvenTop

end IntLInfty.Kan.A83Det

namespace IntLInfty.Kan.A83TauLe

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Tau
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83TauLe

namespace IntLInfty.Kan.A83Wedge

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib Filter Topology
open scoped ContDiff

variable {m r : ℕ}

noncomputable def wRep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) : Ω m :=
  (exists_rep hr w).choose

theorem wRep_spec (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    (IsDeg n (wRep hr w) ∧ IsCr r (wRep hr w)) ∧ jet r (wRep hr w) = w :=
  (exists_rep hr w).choose_spec

end IntLInfty.Kan.A83Wedge

namespace IntLInfty.Kan.A83Gron

open intervalIntegral

end IntLInfty.Kan.A83Gron

namespace IntLInfty.Kan.A83Ev

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83Proj
open scoped ContDiff

section Fam

variable {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem jet_mem (hr : 1 ≤ r) {n : ℕ} {w0 : Ω m} (h : IsDeg n w0 ∧ IsCr r w0) :
    jet r w0 ∈ CrForms r m n := by
  rw [← SetLike.mem_coe, crForms_eq_image hr n]
  exact ⟨_, h, rfl⟩

end Fam

section Lift

variable {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end Lift

end IntLInfty.Kan.A83Ev

namespace IntLInfty.Kan.A83Ev

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83Proj
open scoped ContDiff

section AmbVal

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end AmbVal

end IntLInfty.Kan.A83Ev

namespace IntLInfty.Kan.A83Defect

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83Defect

namespace IntLInfty.Kan.A83Defect

end IntLInfty.Kan.A83Defect

namespace IntLInfty.Kan.A83IntegK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83Defect

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

variable [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83IntegK

namespace IntLInfty.Kan.A83IntegK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83Defect

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83IntegK

namespace IntLInfty.Kan.A83Top

open IntLInfty.Kan
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

variable [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83Top

namespace IntLInfty.Kan.A83IFT

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end IntLInfty.Kan.A83IFT

namespace IntLInfty.Kan.A83KK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem cB_cB (y : Fin m → ℝ) (a : Alg m) : cB m y (cB m y a) = 0 := by
  rw [cB_apply, cB_apply]
  exact CliffordAlgebra.contractLeft_contractLeft _ _

theorem Kop_Kop (p n : ℕ) (β : Ω m) : Kop p (Kop n β) = 0 := by
  funext y
  have key : ∀ s : ℝ, s ^ p • Kop n β (s • y) = cB m y (s ^ p • s • coneInt n β (s • y)) := by
    intro s
    simp only [Kop, map_smul, FunLike.coe_smul, Pi.smul_apply]
  show cB m y (∫ s in (0 : ℝ)..1, s ^ p • Kop n β (s • y)) = 0
  simp_rw [key]
  by_cases hi : IntervalIntegrable
      (fun s : ℝ => cB m y (s ^ p • s • coneInt n β (s • y))) MeasureTheory.volume 0 1
  · rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hi]
    simp [cB_cB]
  · rw [intervalIntegral.integral_undef hi, map_zero]

theorem contDiffOn_Kop (r n : ℕ) {β : Ω m} (hβ : ContDiffOn ℝ r β (simplex m)) :
    ContDiffOn ℝ r (Kop n β) (simplex m) :=
  ContDiffOn.clm_apply ((cB m).contDiff.contDiffOn)
    (contDiffOn_coneInt (isCompact_simplex m) (A83.convex_simplex m) (zero_mem_simplex m)
      (A83.uniqueDiffOn_simplex m) r β n hβ)

theorem isDeg_Kop {n : ℕ} {β : Ω m} (hβc : ContinuousOn β (simplex m)) (hD : IsDeg (n + 1) β) :
    IsDeg n (Kop n β) := by
  intro x hx
  have hmem := coneInt_mem_alg (p := n) (⋀[ℝ]^(n + 1) (Module.Dual ℝ (Fin m → ℝ)))
    (A83.convex_simplex m) (zero_mem_simplex m) hβc hD hx
  have := (contract_mem m (Module.Dual.eval ℝ (Fin m → ℝ) x) (n + 1) _ hmem).1
  simpa [Kop, cB_apply] using this

theorem extD_Kop (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    FormEqOn (extD (Kop n β)) (β - Kop (n + 1) (extD β)) := fun x hx => by
  rw [Pi.sub_apply, ← Kop_hom hr hC hD x hx, add_sub_cancel_right]

theorem isCr_Kop (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    IsCr r (Kop n β) := by
  have hβC : ContDiffOn ℝ r β (simplex m) := contDiffOn_of_coeff fun I => (hC I).1
  have hdC : ContDiffOn ℝ r (extD β) (simplex m) := contDiffOn_of_coeff fun I => (hC I).2
  have h1 := contDiffOn_Kop r n hβC
  have h2 : ContDiffOn ℝ r (β - Kop (n + 1) (extD β)) (simplex m) :=
    hβC.sub (contDiffOn_Kop r (n + 1) hdC)
  intro I
  refine ⟨?_, ?_⟩
  · rw [coeff_eq_coeffL]
    exact (coeffL m I).contDiff.comp_contDiffOn h1
  · refine ((coeffL m I).contDiff.comp_contDiffOn h2).congr fun x hx => ?_
    simp only [coeff_eq_coeffL, Function.comp_apply]
    rw [extD_Kop hr hC hD x hx]

theorem Kop_dKop (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    FormEqOn (Kop n (extD (Kop n β))) (Kop n β) := by
  intro y hy
  have hβc : ContinuousOn β (simplex m) :=
    (contDiffOn_of_coeff (r := r) fun I => (hC I).1).continuousOn
  have hKc : ContinuousOn (Kop (n + 1) (extD β)) (simplex m) :=
    (contDiffOn_Kop r (n + 1) (contDiffOn_of_coeff fun I => (hC I).2)).continuousOn
  rw [Kop_congr n (extD_Kop hr hC hD) y hy, Kop_sub n hβc hKc y hy, Pi.sub_apply, Kop_Kop,
    Pi.zero_apply, sub_zero]

theorem abs_coeff_le_jet {ω : Ω m} (hω : IsCr r ω) (I : Finset (Fin m)) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : |coeff ω I x| ≤ ‖jet r ω‖ := by
  let j0 : Fin (r + 1) := 0
  have hj0 : (j0 : ℕ) = 0 := rfl
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have e1 : (jet r ω).1 I j0 β0 ⟨x, hx⟩ = coeff ω I x := jetComp_zero (hω I).1 hj0 β0 hx
  rw [← e1, ← Real.norm_eq_abs]
  have a1 : ‖(jet r ω).1 I j0 β0 ⟨x, hx⟩‖ ≤ ‖(jet r ω).1 I j0 β0‖ :=
    BoundedContinuousFunction.norm_coe_le_norm _ _
  have a2 : ‖(jet r ω).1 I j0 β0‖ ≤ ‖(jet r ω).1 I j0‖ := norm_le_pi_norm _ β0
  have a3 : ‖(jet r ω).1 I j0‖ ≤ ‖(jet r ω).1 I‖ := norm_le_pi_norm _ j0
  have a4 : ‖(jet r ω).1 I‖ ≤ ‖(jet r ω).1‖ := norm_le_pi_norm (f := ((jet r ω).1 :
    (I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ))) I
  have a5 : ‖(jet r ω).1‖ ≤ ‖jet r ω‖ := norm_fst_le _
  linarith

theorem norm_le_jet : ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : Ω m, IsCr r ω → ∀ x ∈ simplex m,
    ‖ω x‖ ≤ C * ‖jet r ω‖ := by
  refine ⟨∑ I, ‖formBasis m I‖, Finset.sum_nonneg fun I _ => norm_nonneg _,
    fun ω hω x hx => ?_⟩
  conv_lhs => rw [← (formBasis m).sum_repr (ω x)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun I _ => ?_
  rw [norm_smul]
  have hc : ‖(formBasis m).repr (ω x) I‖ ≤ ‖jet r ω‖ := by
    simpa [coeff, Real.norm_eq_abs] using abs_coeff_le_jet hω I hx
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (mul_comm _ _)

end IntLInfty.Kan.A83KK

namespace IntLInfty.Kan.A83KL

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem contOn_of_isCr {ω : Ω m} (hω : IsCr r ω) : ContinuousOn ω (simplex m) :=
  (contDiffOn_of_coeff (r := r) fun I => (hω I).1).continuousOn

theorem kmem (hr : 1 ≤ r) {n : ℕ} {ω : Ω m} (h : IsDeg (n + 1) ω ∧ IsCr r ω) :
    jet r (Kop n ω) ∈ CrForms r m n :=
  A83Ev.jet_mem hr ⟨isDeg_Kop (contOn_of_isCr h.2) h.1, isCr_Kop hr h.2 h.1⟩

theorem dmem (hr : 1 ≤ r) {n : ℕ} {ω : Ω m} (h : IsDeg n ω ∧ IsCr r ω) :
    jet r (extD ω) ∈ CrForms r m (n + 1) :=
  A83Ev.jet_mem hr ⟨isDeg_extD hr h.2 h.1, isCr_extD hr h.2⟩

noncomputable def KLin (hr : 1 ≤ r) (n : ℕ) : CrForms r m (n + 1) →ₗ[ℝ] CrForms r m n where
  toFun w := ⟨jet r (Kop n (A83Wedge.wRep hr w)), kmem hr (A83Wedge.wRep_spec hr w).1⟩
  map_add' w w' := by
    have h1 := A83Wedge.wRep_spec hr (w + w')
    have h2 := A83Wedge.wRep_spec hr w
    have h3 := A83Wedge.wRep_spec hr w'
    have hs : IsCr r (A83Wedge.wRep hr w + A83Wedge.wRep hr w') := isCr_add hr h2.1.2 h3.1.2
    have e : jet r (A83Wedge.wRep hr (w + w')) =
        jet r (A83Wedge.wRep hr w + A83Wedge.wRep hr w') := by
      rw [jet_add hr h2.1.2 h3.1.2, h1.2, h2.2, h3.2]
      try rfl
    apply Subtype.ext
    show jet r (Kop n (A83Wedge.wRep hr (w + w'))) =
      jet r (Kop n (A83Wedge.wRep hr w)) + jet r (Kop n (A83Wedge.wRep hr w'))
    rw [jet_congr (Kop_congr n (formEqOn_of_jet h1.1.2 hs e)),
      jet_congr (Kop_add n (contOn_of_isCr h2.1.2) (contOn_of_isCr h3.1.2)),
      jet_add hr (isCr_Kop hr h2.1.2 h2.1.1) (isCr_Kop hr h3.1.2 h3.1.1)]
  map_smul' c w := by
    have h1 := A83Wedge.wRep_spec hr (c • w)
    have h2 := A83Wedge.wRep_spec hr w
    have hs : IsCr r (c • A83Wedge.wRep hr w) := isCr_smul hr c h2.1.2
    have e : jet r (A83Wedge.wRep hr (c • w)) = jet r (c • A83Wedge.wRep hr w) := by
      rw [jet_smul hr c h2.1.2, h1.2, h2.2]
      try rfl
    apply Subtype.ext
    show jet r (Kop n (A83Wedge.wRep hr (c • w))) = c • jet r (Kop n (A83Wedge.wRep hr w))
    rw [jet_congr (Kop_congr n (formEqOn_of_jet h1.1.2 hs e)), jet_congr (Kop_smul n c _),
      jet_smul hr c (isCr_Kop hr h2.1.2 h2.1.1)]

theorem KLin_val (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m (n + 1)) {ω : Ω m}
    (hC : IsCr r ω) (h : jet r ω = w) :
    (KLin hr n w : Jet r m × Jet r m) = jet r (Kop n ω) := by
  have h1 := A83Wedge.wRep_spec hr w
  exact jet_congr (Kop_congr n (formEqOn_of_jet h1.1.2 hC (by rw [h1.2, h])))

noncomputable def dLin (hr : 1 ≤ r) (n : ℕ) : CrForms r m n →ₗ[ℝ] CrForms r m (n + 1) where
  toFun w := ⟨jet r (extD (A83Wedge.wRep hr w)), dmem hr (A83Wedge.wRep_spec hr w).1⟩
  map_add' w w' := by
    have h1 := A83Wedge.wRep_spec hr (w + w')
    have h2 := A83Wedge.wRep_spec hr w
    have h3 := A83Wedge.wRep_spec hr w'
    have hs : IsCr r (A83Wedge.wRep hr w + A83Wedge.wRep hr w') := isCr_add hr h2.1.2 h3.1.2
    have e : jet r (A83Wedge.wRep hr (w + w')) =
        jet r (A83Wedge.wRep hr w + A83Wedge.wRep hr w') := by
      rw [jet_add hr h2.1.2 h3.1.2, h1.2, h2.2, h3.2]
      try rfl
    apply Subtype.ext
    show jet r (extD (A83Wedge.wRep hr (w + w'))) =
      jet r (extD (A83Wedge.wRep hr w)) + jet r (extD (A83Wedge.wRep hr w'))
    rw [jet_congr (extD_congr (formEqOn_of_jet h1.1.2 hs e)),
      jet_congr (show FormEqOn (extD (A83Wedge.wRep hr w + A83Wedge.wRep hr w'))
        (extD (A83Wedge.wRep hr w) + extD (A83Wedge.wRep hr w')) from
        fun x hx => extD_add hr h2.1.2 h3.1.2 hx), jet_add hr
      (isCr_extD hr h2.1.2) (isCr_extD hr h3.1.2)]
  map_smul' c w := by
    have h1 := A83Wedge.wRep_spec hr (c • w)
    have h2 := A83Wedge.wRep_spec hr w
    have hs : IsCr r (c • A83Wedge.wRep hr w) := isCr_smul hr c h2.1.2
    have e : jet r (A83Wedge.wRep hr (c • w)) = jet r (c • A83Wedge.wRep hr w) := by
      rw [jet_smul hr c h2.1.2, h1.2, h2.2]
      try rfl
    apply Subtype.ext
    show jet r (extD (A83Wedge.wRep hr (c • w))) = c • jet r (extD (A83Wedge.wRep hr w))
    rw [jet_congr (extD_congr (formEqOn_of_jet h1.1.2 hs e)),
      jet_congr (show FormEqOn (extD (c • A83Wedge.wRep hr w))
        (c • extD (A83Wedge.wRep hr w)) from fun x hx => extD_smul hr c h2.1.2 hx),
      jet_smul hr c (isCr_extD hr h2.1.2)]

theorem dLin_val (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) {ω : Ω m}
    (hC : IsCr r ω) (h : jet r ω = w) :
    (dLin hr n w : Jet r m × Jet r m) = jet r (extD ω) := by
  have h1 := A83Wedge.wRep_spec hr w
  exact jet_congr (extD_congr (formEqOn_of_jet h1.1.2 hC (by rw [h1.2, h])))

theorem coeffTendsto_extD_of_jet {ωk : ℕ → Ω m} {ω : Ω m} (hk : ∀ k, IsCr r (ωk k))
    (hω : IsCr r ω) (h : Tendsto (fun k => jet r (ωk k)) atTop (𝓝 (jet r ω))) :
    CoeffTendsto (fun k => extD (ωk k)) (extD ω) := by
  intro I x hx
  let j0 : Fin (r + 1) := 0
  have hj0 : (j0 : ℕ) = 0 := rfl
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have hc : Continuous (fun w : Jet r m × Jet r m => w.2 I j0 β0 ⟨x, hx⟩) :=
    (continuous_eval_const _).comp
      ((continuous_jet_eval I j0 β0).comp continuous_snd)
  have t := (hc.tendsto _).comp h
  have e1 : (jet r ω).2 I j0 β0 ⟨x, hx⟩ = coeff (extD ω) I x := jetComp_zero (hω I).2 hj0 β0 hx
  rw [Function.comp_def, e1] at t
  exact t.congr fun k => jetComp_zero ((hk k) I).2 hj0 β0 hx

theorem tendsto_of_coeffTendsto {ωk : ℕ → Ω m} {ω : Ω m} (h : CoeffTendsto ωk ω) {y : Fin m → ℝ}
    (hy : y ∈ simplex m) : Tendsto (fun k => ωk k y) atTop (𝓝 (ω y)) := by
  have e : ∀ θ : Ω m, θ y = ∑ I, coeff θ I y • formBasis m I := fun θ => by
    simp only [coeff]
    exact ((formBasis m).sum_repr (θ y)).symm
  rw [e ω]
  simp_rw [e]
  exact tendsto_finsetSum _ fun I _ => (h I y hy).smul_const _

theorem coeffTendsto_Kop (n : ℕ) {ωk : ℕ → Ω m} {ω : Ω m} (hk : ∀ k, ContinuousOn (ωk k) (simplex m))
    (h : CoeffTendsto ωk ω) {B : ℝ} (hB : ∀ k, ∀ y ∈ simplex m, ‖ωk k y‖ ≤ B) :
    CoeffTendsto (fun k => Kop n (ωk k)) (Kop n ω) := by
  intro I x hx
  have hint : Tendsto (fun k => coneInt n (ωk k) x) atTop (𝓝 (coneInt n ω x)) := by
    unfold coneInt
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B)
      (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_)
      intervalIntegrable_const ?_
    · have hc : ContinuousOn (fun t : ℝ => t ^ n • ωk k (t • x)) (Set.Icc (0 : ℝ) 1) :=
        (continuous_pow n).continuousOn.smul ((hk k).comp
          (continuous_id.smul continuous_const).continuousOn
          (fun t ht => smul_mem_simplex hx ht))
      rw [Set.uIoc_of_le zero_le_one]
      exact (hc.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · refine MeasureTheory.ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
      rw [norm_smul, norm_pow, Real.norm_of_nonneg ht'.1]
      have hp : t ^ n ≤ 1 := pow_le_one₀ ht'.1 ht'.2
      have hp0 : 0 ≤ t ^ n := pow_nonneg ht'.1 n
      have hb := hB k _ (smul_mem_simplex hx ht')
      have h0 : 0 ≤ ‖ωk k (t • x)‖ := norm_nonneg _
      nlinarith
    · refine MeasureTheory.ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact (tendsto_of_coeffTendsto h (smul_mem_simplex hx (Set.Ioc_subset_Icc_self ht))).const_smul
        (t ^ n)
  have hc : Continuous fun a : Alg m => coeffL m I (cB m x a) :=
    (coeffL m I).continuous.comp (cB m x).continuous
  have := (hc.tendsto _).comp hint
  simpa only [coeff_eq_coeffL, Kop, Function.comp_def] using this

theorem KLin_continuous (hr : 1 ≤ r) (n : ℕ) : Continuous (KLin (m := m) hr n) := by
  haveI := crForms_complete r m (n + 1)
  haveI := crForms_complete r m n
  refine (KLin hr n).continuous_of_seq_closed_graph fun u w z hu hz => ?_
  choose ωk hωk hk using fun k => exists_rep hr (u k)
  obtain ⟨ω, hω, hw⟩ := exists_rep hr w
  obtain ⟨ωz, hωz, hzj⟩ := exists_rep hr z
  have hval : ∀ k, (KLin hr n (u k) : Jet r m × Jet r m) = jet r (Kop n (ωk k)) :=
    fun k => KLin_val hr (u k) (hωk k).2 (hk k)
  have hju : Tendsto (fun k => jet r (ωk k)) atTop (𝓝 (jet r ω)) := by
    have := (continuous_subtype_val.tendsto w).comp hu
    rw [hw]
    exact this.congr fun k => (hk k).symm
  have t1 : CoeffTendsto (fun k => Kop n (ωk k)) ωz := by
    refine coeffTendsto_of_jet (fun k => isCr_Kop hr (hωk k).2 (hωk k).1) hωz.2 ?_
    have := (continuous_subtype_val.tendsto z).comp hz
    rw [hzj]
    exact this.congr fun k => hval k
  obtain ⟨C, hC0, hC⟩ := norm_le_jet (m := m) (r := r)
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hju).exists_norm_le
  have t2 : CoeffTendsto (fun k => Kop n (ωk k)) (Kop n ω) :=
    coeffTendsto_Kop n (fun k => contOn_of_isCr (hωk k).2)
      (coeffTendsto_of_jet (fun k => (hωk k).2) hω.2 hju) (B := C * M) fun k y hy =>
        (hC _ (hωk k).2 y hy).trans (mul_le_mul_of_nonneg_left (hM _ ⟨k, rfl⟩) hC0)
  apply Subtype.ext
  show (z : Jet r m × Jet r m) = (KLin hr n w : Jet r m × Jet r m)
  rw [KLin_val hr w hω.2 hw, ← hzj]
  exact jet_congr (coeffTendsto_unique t1 t2)

theorem dLin_continuous (hr : 1 ≤ r) (n : ℕ) : Continuous (dLin (m := m) hr n) := by
  haveI := crForms_complete r m (n + 1)
  haveI := crForms_complete r m n
  refine (dLin hr n).continuous_of_seq_closed_graph fun u w z hu hz => ?_
  choose ωk hωk hk using fun k => exists_rep hr (u k)
  obtain ⟨ω, hω, hw⟩ := exists_rep hr w
  obtain ⟨ωz, hωz, hzj⟩ := exists_rep hr z
  have hval : ∀ k, (dLin hr n (u k) : Jet r m × Jet r m) = jet r (extD (ωk k)) :=
    fun k => dLin_val hr (u k) (hωk k).2 (hk k)
  have hju : Tendsto (fun k => jet r (ωk k)) atTop (𝓝 (jet r ω)) := by
    have := (continuous_subtype_val.tendsto w).comp hu
    rw [hw]
    exact this.congr fun k => (hk k).symm
  have t1 : CoeffTendsto (fun k => extD (ωk k)) ωz := by
    refine coeffTendsto_of_jet (fun k => isCr_extD hr (hωk k).2) hωz.2 ?_
    have := (continuous_subtype_val.tendsto z).comp hz
    rw [hzj]
    exact this.congr fun k => hval k
  have t2 : CoeffTendsto (fun k => extD (ωk k)) (extD ω) :=
    coeffTendsto_extD_of_jet (fun k => (hωk k).2) hω.2 hju
  apply Subtype.ext
  show (z : Jet r m × Jet r m) = (dLin hr n w : Jet r m × Jet r m)
  rw [dLin_val hr w hω.2 hw, ← hzj]
  exact jet_congr (coeffTendsto_unique t1 t2)

noncomputable def KCLM (hr : 1 ≤ r) (n : ℕ) : CrForms r m (n + 1) →L[ℝ] CrForms r m n :=
  ⟨KLin hr n, KLin_continuous hr n⟩

noncomputable def dCLM (hr : 1 ≤ r) (n : ℕ) : CrForms r m n →L[ℝ] CrForms r m (n + 1) :=
  ⟨dLin hr n, dLin_continuous hr n⟩

noncomputable def HCLM (hr : 1 ≤ r) (n : ℕ) : CrForms r m n →L[ℝ] CrForms r m n :=
  (KCLM hr n).comp (dCLM hr n)

theorem HCLM_val (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) {ω : Ω m} (hD : IsDeg n ω)
    (hC : IsCr r ω) (h : jet r ω = w) :
    (HCLM hr n w : Jet r m × Jet r m) = jet r (Kop n (extD ω)) := by
  show (KLin hr n (dLin hr n w) : Jet r m × Jet r m) = _
  exact KLin_val hr _ (isCr_extD hr hC) (dLin_val hr w hC h).symm

theorem HCLM_idem (hr : 1 ≤ r) (n : ℕ) : (HCLM (m := m) hr n).comp (HCLM hr n) = HCLM hr n := by
  ext1 w
  obtain ⟨ω, hω, hw⟩ := exists_rep hr w
  have hD1 : IsDeg (n + 1) (extD ω) := isDeg_extD hr hω.2 hω.1
  have hC1 : IsCr r (extD ω) := isCr_extD hr hω.2
  have hKD : IsDeg n (Kop n (extD ω)) := isDeg_Kop (contOn_of_isCr hC1) hD1
  have hKC : IsCr r (Kop n (extD ω)) := isCr_Kop hr hC1 hD1
  apply Subtype.ext
  show (HCLM hr n (HCLM hr n w) : Jet r m × Jet r m) = HCLM hr n w
  rw [HCLM_val hr (HCLM hr n w) hKD hKC (HCLM_val hr w hω.1 hω.2 hw).symm,
    HCLM_val hr w hω.1 hω.2 hw]
  exact jet_congr (Kop_dKop hr hC1 hD1)

end IntLInfty.Kan.A83KL

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj

attribute [local instance] algNAG algNS algFD

theorem map_contractLeft {m m' : ℕ} (f : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (x : Fin m → ℝ)
    (a : Alg m') :
    ExteriorAlgebra.map f.dualMap
        (CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m' → ℝ) (f x)) a) =
      CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) x)
        (ExteriorAlgebra.map f.dualMap a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap c =>
    rw [CliffordAlgebra.contractLeft_algebraMap, AlgHom.commutes,
      CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | ι_mul a φ ha =>
    have hι : ExteriorAlgebra.map f.dualMap (CliffordAlgebra.ι _ φ) =
        CliffordAlgebra.ι _ (f.dualMap φ) := ExteriorAlgebra.map_apply_ι _ _
    rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, map_mul, hι,
      CliffordAlgebra.contractLeft_ι_mul, ← ha]
    simp [LinearMap.dualMap_apply]

theorem Kop_pullLin {m m' : ℕ} (n : ℕ) (f : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (β : Ω m')
    (x : Fin m → ℝ)
    (hβ : IntervalIntegrable (fun t : ℝ => (t ^ n) • β (t • f x)) MeasureTheory.volume 0 1) :
    ExteriorAlgebra.map f.dualMap (Kop n β (f x)) =
      Kop n (fun y => ExteriorAlgebra.map f.dualMap (β (f y))) x := by
  let G : Alg m' →L[ℝ] Alg m :=
    LinearMap.toContinuousLinearMap (ExteriorAlgebra.map f.dualMap).toLinearMap
  have hG : ∀ a, G a = ExteriorAlgebra.map f.dualMap a := fun _ => rfl
  show ExteriorAlgebra.map f.dualMap (cB m' (f x) (coneInt n β (f x))) =
    cB m x (coneInt n (fun y => ExteriorAlgebra.map f.dualMap (β (f y))) x)
  rw [cB_apply, cB_apply, map_contractLeft]
  congr 1
  unfold coneInt
  rw [← hG, ← G.intervalIntegral_comp_comm hβ]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [map_smul, hG]

theorem coface_eq_lin {m : ℕ} (i : Fin (m + 2)) (hi : i ≠ 0) (x : Fin m → ℝ) :
    coface m i x = cofaceLin m i x := by
  have h0 : i.succAbove 0 = 0 := Fin.succAbove_ne_zero_zero hi
  simp [coface, h0, vertex]

theorem pull_Kop {m : ℕ} (n : ℕ) (i : Fin (m + 2)) (hi : i ≠ 0) {β : Ω (m + 1)}
    (hβ : ContinuousOn β (simplex (m + 1))) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    pull m i (Kop n β) x = Kop n (pull m i β) x := by
  have hfx : cofaceLin m i x ∈ simplex (m + 1) := by
    rw [← coface_eq_lin i hi]; exact coface_mem i hx
  have hint := intervalIntegrable_cone (A83.convex_simplex (m + 1)) (zero_mem_simplex (m + 1))
    hβ n hfx
  have hp : pull m i β = fun y => ExteriorAlgebra.map (cofaceLin m i).dualMap
      (β (cofaceLin m i y)) := by
    funext y; simp only [pull, coface_eq_lin i hi]
  show ExteriorAlgebra.map (cofaceLin m i).dualMap (Kop n β (coface m i x)) = _
  rw [coface_eq_lin i hi, hp]
  exact Kop_pullLin n (cofaceLin m i) β x hint

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL

attribute [local instance] algNAG algNS algFD

theorem faceCr_KCLM {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) (hi : i ≠ 0)
    (w : CrForms r (m + 1) (n + 1)) :
    faceCr r m n i (KCLM hr n w) = KCLM hr n (faceCr r m (n + 1) i w) := by
  obtain ⟨⟨hD, hC⟩, hj⟩ := A83Wedge.wRep_spec hr w
  set ω := A83Wedge.wRep hr w
  have hK : jet r (Kop n ω) = (KCLM hr n w : Jet r (m + 1) × Jet r (m + 1)) :=
    (KLin_val hr w hC hj).symm
  have hF : jet r (pull m i ω) = (faceCr r m (n + 1) i w : Jet r m × Jet r m) :=
    (faceCr_val hr i w hD hC hj).symm
  apply Subtype.ext
  rw [faceCr_val hr i (KCLM hr n w) (isDeg_Kop (continuousOn_of_isCr hC) hD) (isCr_Kop hr hC hD) hK]
  show _ = (KLin hr n (faceCr r m (n + 1) i w) : Jet r m × Jet r m)
  rw [KLin_val hr (faceCr r m (n + 1) i w) (pull_isCr hr i hC) hF]
  exact jet_congr fun x hx => pull_Kop n i hi (continuousOn_of_isCr hC) hx

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83C1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83K1

attribute [local instance] algNAG algNS algFD algComplete

theorem faceCr_dCLM' {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2))
    (w : CrForms r (m + 1) n) :
    faceCr r m (n + 1) i (dCLM hr n w) = dCLM hr n (faceCr r m n i w) := by
  obtain ⟨om, hom, hw⟩ := exists_rep hr w
  have hd : (dCLM hr n w : Jet r (m + 1) × Jet r (m + 1)) = jet r (extD om) :=
    dLin_val hr w hom.2 hw
  have hF : jet r (pull m i om) = (faceCr r m n i w : Jet r m × Jet r m) :=
    (faceCr_val hr i w hom.1 hom.2 hw).symm
  apply Subtype.ext
  rw [faceCr_val hr i (dCLM hr n w) (isDeg_extD hr hom.2 hom.1) (isCr_extD hr hom.2) hd.symm]
  show _ = (dLin hr n (faceCr r m n i w) : Jet r m × Jet r m)
  rw [dLin_val hr _ (pull_isCr hr i hom.2) hF]
  exact jet_congr fun x hx => (extD_pull hr i (fun I => (hom.2 I).1) hx).symm

theorem KCLM_val' {r m : ℕ} (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m (n + 1)) {ω : Ω m}
    (hC : IsCr r ω) (h : jet r ω = w) :
    (KCLM hr n w : Jet r m × Jet r m) = jet r (Kop n ω) := KLin_val hr w hC h

theorem dCLM_val' {r m : ℕ} (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) {ω : Ω m}
    (hC : IsCr r ω) (h : jet r ω = w) :
    (dCLM hr n w : Jet r m × Jet r m) = jet r (extD ω) := dLin_val hr w hC h

theorem dK_Kd {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) (w : CrForms r m (n + 1)) :
    dCLM hr n (KCLM hr n w) + KCLM hr (n + 1) (dCLM hr (n + 1) w) = w := by
  obtain ⟨ω, ⟨hD, hC⟩, hw⟩ := exists_rep hr w
  have hK := KCLM_val' hr w hC hw
  have hKC : IsCr r (Kop n ω) := isCr_Kop hr hC hD
  have hdK := dCLM_val' hr (KCLM hr n w) hKC hK.symm
  have hd := dCLM_val' hr w hC hw
  have hdC : IsCr r (extD ω) := isCr_extD hr hC
  have hKd := KCLM_val' hr (dCLM hr (n + 1) w) hdC hd.symm
  have hKdC : IsCr r (Kop (n + 1) (extD ω)) := isCr_Kop hr hdC (isDeg_extD hr hC hD)
  apply Subtype.ext
  rw [Submodule.coe_add, hdK, hKd, ← jet_add hr (isCr_extD hr hKC) hKdC, ← hw]
  exact jet_congr (Kop_hom hr hC hD)

theorem KK_zero {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) (w : CrForms r m (n + 2)) :
    KCLM hr n (KCLM hr (n + 1) w) = 0 := by
  obtain ⟨ω, ⟨hD, hC⟩, hw⟩ := exists_rep hr w
  have hK := KCLM_val' hr w hC hw
  have hKK := KCLM_val' hr (KCLM hr (n + 1) w) (isCr_Kop hr hC hD) hK.symm
  apply Subtype.ext
  rw [hKK, Kop_Kop, jet_zero' hr]
  rfl

theorem dd_zero {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) (w : CrForms r m n) :
    dCLM hr (n + 1) (dCLM hr n w) = 0 := by
  obtain ⟨ω, ⟨hD, hC⟩, hw⟩ := exists_rep hr w
  have hd := dCLM_val' hr w hC hw
  have hdd := dCLM_val' hr (dCLM hr n w) (isCr_extD hr hC) hd.symm
  apply Subtype.ext
  rw [hdd, jet_congr (show FormEqOn (extD (extD ω)) 0 from fun x hx => extD_extD hr hC x hx),
    jet_zero' hr]
  rfl

theorem Kop_coord {r m n : ℕ} {β : Ω m} (hC : IsCr r β) {y : Fin m → ℝ} (hy : y ∈ simplex m) :
    Kop n β y = CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) y)
      (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1, s ^ n * coeff β I (s • y)) • formBasis m I) := by
  show cB m y (coneInt n β y) = _
  rw [cB_apply]
  congr 1
  conv_lhs => rw [← (formBasis m).sum_repr (coneInt n β y)]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  rw [← coeffL_apply]
  unfold coneInt
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (intervalIntegrable_cone
    (A83.convex_simplex m) (zero_mem_simplex m) (continuousOn_of_isCr hC) n hy)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [coeffL_apply, coeff, map_smul, Finsupp.smul_apply, smul_eq_mul]

end IntLInfty.Kan.A83C1

open IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83K1 IntLInfty.Kan.A83C1 in
theorem solution (r : ℕ) (hr : 1 ≤ r)
    (Kc : ∀ m : ℕ, ℕ → IntLInfty.Kan.Ω m → IntLInfty.Kan.Ω m)
    (hKc : ∀ (m n : ℕ) (β : IntLInfty.Kan.Ω m) (y : Fin m → ℝ),
      letI : NormedAddCommGroup (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
        NormedAddCommGroup.induced (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
          (Finset (Fin m) → ℝ) (IntLInfty.Kan.formBasis m).equivFun.toLinearMap
          (IntLInfty.Kan.formBasis m).equivFun.injective
      letI : NormedSpace ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
        NormedSpace.induced ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
          (Finset (Fin m) → ℝ) (IntLInfty.Kan.formBasis m).equivFun.toLinearMap
      Kc m n β y = CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) y)
        (∫ t in (0 : ℝ)..1, t ^ n • β (t • y))) :
    (∀ (m n : ℕ) (β : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r β → IntLInfty.Kan.IsDeg (n + 1) β →
      IntLInfty.Kan.IsDeg n (Kc m n β) ∧ IntLInfty.Kan.IsCr r (Kc m n β) ∧
      ∀ x ∈ IntLInfty.Kan.simplex m,
        IntLInfty.Kan.extD (Kc m n β) x + Kc m (n + 1) (IntLInfty.Kan.extD β) x = β x) ∧
    (∀ (m p n : ℕ) (β : IntLInfty.Kan.Ω m), Kc m p (Kc m n β) = 0) ∧
    (∀ (m n : ℕ) (β β' : IntLInfty.Kan.Ω m), (∀ x ∈ IntLInfty.Kan.simplex m, β x = β' x) →
      ∀ x ∈ IntLInfty.Kan.simplex m, Kc m n β x = Kc m n β' x) ∧
    (∀ (m n : ℕ) (β β' : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r β → IntLInfty.Kan.IsCr r β' →
      ∀ x ∈ IntLInfty.Kan.simplex m, Kc m n (β + β') x = Kc m n β x + Kc m n β' x) ∧
    (∀ (m n : ℕ) (c : ℝ) (β : IntLInfty.Kan.Ω m) (x : Fin m → ℝ), Kc m n (c • β) x = c • Kc m n β x) ∧
    (∀ (m n : ℕ) (i : Fin (m + 2)), i ≠ 0 → ∀ β : IntLInfty.Kan.Ω (m + 1), IntLInfty.Kan.IsCr r β →
      ∀ x ∈ IntLInfty.Kan.simplex m,
        IntLInfty.Kan.pull m i (Kc (m + 1) n β) x = Kc m n (IntLInfty.Kan.pull m i β) x) ∧
    (∀ (m n : ℕ) (ω : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r ω → IntLInfty.Kan.IsDeg n ω →
      IntLInfty.Kan.IsDeg (n + 1) (IntLInfty.Kan.extD ω)) ∧
    (∀ (m : ℕ) (ω : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r ω →
      IntLInfty.Kan.IsCr r (IntLInfty.Kan.extD ω)) ∧
    (∀ (m n : ℕ) (β : IntLInfty.Kan.Ω m), IntLInfty.Kan.IsCr r β → ∀ y ∈ IntLInfty.Kan.simplex m,
      Kc m n β y = CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) y)
        (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1, s ^ n * IntLInfty.Kan.coeff β I (s • y)) •
          IntLInfty.Kan.formBasis m I)) ∧
    ∃ (K : ∀ m n : ℕ, IntLInfty.Kan.CrForms r m (n + 1) →L[ℝ] IntLInfty.Kan.CrForms r m n)
      (d : ∀ m n : ℕ, IntLInfty.Kan.CrForms r m n →L[ℝ] IntLInfty.Kan.CrForms r m (n + 1)),
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m (n + 1)) (ω : IntLInfty.Kan.Ω m),
        IntLInfty.Kan.IsCr r ω → IntLInfty.Kan.jet r ω = w →
        (K m n w : IntLInfty.Kan.Jet r m × IntLInfty.Kan.Jet r m) = IntLInfty.Kan.jet r (Kc m n ω)) ∧
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m n) (ω : IntLInfty.Kan.Ω m),
        IntLInfty.Kan.IsCr r ω → IntLInfty.Kan.jet r ω = w →
        (d m n w : IntLInfty.Kan.Jet r m × IntLInfty.Kan.Jet r m) =
          IntLInfty.Kan.jet r (IntLInfty.Kan.extD ω)) ∧
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m (n + 1)),
        d m n (K m n w) + K m (n + 1) (d m (n + 1) w) = w) ∧
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m (n + 2)), K m n (K m (n + 1) w) = 0) ∧
      (∀ (m n : ℕ) (w : IntLInfty.Kan.CrForms r m n), d m (n + 1) (d m n w) = 0) ∧
      (∀ m n : ℕ, (K m n ∘L d m n) ∘L (K m n ∘L d m n) = K m n ∘L d m n) ∧
      (∀ (m n : ℕ) (i : Fin (m + 2)), i ≠ 0 → ∀ w : IntLInfty.Kan.CrForms r (m + 1) (n + 1),
        IntLInfty.Kan.faceCr r m n i (K (m + 1) n w) = K m n (IntLInfty.Kan.faceCr r m (n + 1) i w)) ∧
      (∀ (m n : ℕ) (i : Fin (m + 2)) (w : IntLInfty.Kan.CrForms r (m + 1) n),
        IntLInfty.Kan.faceCr r m (n + 1) i (d (m + 1) n w) = d m n (IntLInfty.Kan.faceCr r m n i w)) := by
  have hK : Kc = fun m n β => @IntLInfty.Kan.A83Poinc.Kop m n β := by
    funext m n β y
    exact hKc m n β y
  subst hK
  refine ⟨fun m n β hC hD => ⟨isDeg_Kop (continuousOn_of_isCr hC) hD, isCr_Kop hr hC hD,
      Kop_hom hr hC hD⟩,
    fun m p n β => Kop_Kop p n β,
    fun m n β β' h => Kop_congr n h,
    fun m n β β' hC hC' x hx => Kop_add n (continuousOn_of_isCr hC) (continuousOn_of_isCr hC') x hx,
    fun m n c β x => by simp only [Kop, Pi.smul_apply, coneInt_smul', map_smul],
    fun m n i hi β hC x hx => pull_Kop n i hi (continuousOn_of_isCr hC) hx,
    fun m n ω hC hD => isDeg_extD hr hC hD,
    fun m ω hC => isCr_extD hr hC,
    fun m n β hC y hy => Kop_coord hC hy,
    fun m n => KCLM (m := m) hr n, fun m n => dCLM (m := m) hr n,
    fun m n w ω hC h => KCLM_val' hr w hC h,
    fun m n w ω hC h => dCLM_val' hr w hC h,
    fun m n w => dK_Kd hr n w,
    fun m n w => KK_zero hr n w,
    fun m n w => dd_zero hr n w,
    fun m n => HCLM_idem hr n,
    fun m n i hi w => faceCr_KCLM hr n i hi w,
    fun m n i w => faceCr_dCLM' hr n i w⟩

