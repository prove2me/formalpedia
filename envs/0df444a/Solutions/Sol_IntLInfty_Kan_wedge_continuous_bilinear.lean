-- Prove2me | solution 1 for IntLInfty.Kan.wedge_continuous_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:52:07.11926+00:00
-- url     : https://prove2.me/submissions/af12fc5a-ef43-4f25-b47e-b67c718a8ba4

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

/-! Draft for IntLInfty.Kan.theorem_5_10 (a83e3b53). Step K0a: generator systems are nested. -/

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

theorem lowAlg_mono {p q : ℕ} (h : p ≤ q) : lowAlg L p ≤ lowAlg L q := by
  apply Algebra.adjoin_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨k, hk, hx⟩ := hx
  exact ⟨k, hk.trans h, hx⟩

theorem gen_mem_lowAlg {k p : ℕ} (h : k ≤ p) (ξ : Module.Dual ℝ (L k)) :
    gen L k ξ ∈ lowAlg L p := by
  apply Algebra.subset_adjoin
  simp only [Set.mem_iUnion]
  exact ⟨k, h, ξ, rfl⟩

theorem ceDeg_le_lowAlg (n : ℕ) :
    ceDeg L (n + 1) ≤ Subalgebra.toSubmodule (lowAlg L n) := by
  apply Submodule.span_le.mpr
  rintro x ⟨m, d, ξ, hsum, rfl⟩
  apply Subalgebra.list_prod_mem
  intro y hy
  rw [List.mem_ofFn] at hy
  obtain ⟨t, rfl⟩ := hy
  apply gen_mem_lowAlg
  have : d t + 1 ≤ ∑ s, (d s + 1) :=
    Finset.single_le_sum (f := fun s => d s + 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  omega

theorem gen_mem_ceDeg (k : ℕ) (ξ : Module.Dual ℝ (L k)) : gen L k ξ ∈ ceDeg L (k + 1) := by
  apply Submodule.subset_span
  refine ⟨1, fun _ => k, fun _ => ξ, by simp, by simp⟩

theorem one_mem_ceDeg : (1 : CE L) ∈ ceDeg L 0 := by
  apply Submodule.subset_span
  refine ⟨0, Fin.elim0, fun t => Fin.elim0 t, by simp, by simp⟩

theorem delta_one (δ : LInfty L) : δ.δ 1 = 0 := by
  have h := δ.leibniz 0 1 one_mem_ceDeg 1
  simp only [mul_one, pow_zero, one_smul, one_mul] at h
  have h2 : δ.δ 1 + δ.δ 1 = δ.δ 1 := h.symm
  simpa using h2

theorem delta_delta (δ : LInfty L) (x : CE L) : δ.δ (δ.δ x) = 0 := by
  have := congrArg (fun f => f x) δ.sq
  simpa using this

theorem delta_gen_mem (δ : LInfty L) (k : ℕ) (ξ : Module.Dual ℝ (L k)) :
    δ.δ (gen L k ξ) ∈ lowAlg L (k + 1) :=
  ceDeg_le_lowAlg (k + 1) (δ.deg _ _ (gen_mem_ceDeg k ξ))

theorem delta_lowAlg (δ : LInfty L) (p : ℕ) (x : CE L) (hx : x ∈ lowAlg L p) :
    δ.δ x ∈ lowAlg L (p + 1) := by
  have hx' : x ∈ Subalgebra.toSubmodule (lowAlg L p) := hx
  rw [lowAlg, Algebra.adjoin_eq_span] at hx'
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    induction hy using Submonoid.closure_induction_left with
    | one => rw [delta_one]; exact Subalgebra.zero_mem _
    | mul_left a ha b hb ih =>
      simp only [Set.mem_iUnion] at ha
      obtain ⟨k, hk, ξ, rfl⟩ := ha
      have hb' : b ∈ lowAlg L p := by
        have : b ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ
            (⋃ k, ⋃ (_ : k ≤ p), Set.range (gen L k))) := by
          rw [Algebra.adjoin_eq_span]; exact Submodule.subset_span hb
        exact this
      rw [δ.leibniz (k + 1) _ (gen_mem_ceDeg k ξ) b]
      refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ ?_ ?_) (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ ?_ ih) _)
      · exact lowAlg_mono (by omega) (delta_gen_mem δ k ξ)
      · exact lowAlg_mono (by omega) hb'
      · exact gen_mem_lowAlg (by omega) ξ
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Subalgebra.smul_mem _ ha r

theorem imSub_le_kerSub (δ : LInfty L) (i : ℕ) : imSub δ i ≤ kerSub δ i := by
  cases i with
  | zero => simp [imSub]
  | succ p =>
    intro ξ hξ
    simp only [imSub, Submodule.mem_map, Submodule.mem_comap, LinearMap.snd_apply] at hξ
    obtain ⟨⟨η, ξ'⟩, ha, rfl⟩ := hξ
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Subalgebra.mem_toSubmodule] at ha
    show δ.δ (gen L (p + 1) ξ') ∈ lowAlg L (p + 1)
    have hg : gen L (p + 1) ξ' = δ.δ (gen L p η) - (δ.δ (gen L p η) - gen L (p + 1) ξ') := by abel
    rw [hg, map_sub, delta_delta, zero_sub]
    exact Subalgebra.neg_mem _ (delta_lowAlg δ p _ ha)

theorem K0a (δ : LInfty L) :
    (∀ n i, tauLt δ n i ≤ tauLe δ n i) ∧ (∀ n i, tauLe δ n i ≤ tauLt δ (n + 1) i) := by
  constructor
  · intro n i
    simp only [tauLt, tauLe]
    split_ifs
    · exact le_rfl
    · subst_vars; exact imSub_le_kerSub δ _
    · exact le_rfl
  · intro n i
    simp only [tauLt, tauLe]
    split_ifs <;> first | exact le_rfl | exact le_top | exact bot_le | omega

/-! ## Forms: the simplex is a domain of unique differentiability; the jet map is linear on Cʳ forms -/

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

end JetClosed

theorem crForms_eq_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} := by
  rw [crForms_coe hr n, (jetImage_closed hr n).closure_eq]

section ClosedSpan

variable {m r : ℕ}

end ClosedSpan

section Rep

/-! Representative independence: the jet of a form only depends on its values on the simplex, and
it determines those values; hence `faceCr`, `faceCl`, `dCr` are computed by any representative. -/

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

end Rep

section Pull

/-! Pullback along cofaces preserves degree and the `Cʳ` condition, and commutes with `d`. -/

variable {m r : ℕ}

end Pull

section PullAff

/-! Pullback along an arbitrary affine map `x ↦ b + L x` sending `Δᵐ` into `Δᵐ'` (the retractions
used by the horn-extension operator of Lemma 5.9 are of this kind). -/

variable {m m' r : ℕ}

end PullAff

section PullS

/-! Simplicial pullbacks: the affine map `Δᵐ → Δᵐ'` sending the vertex `v_l` to `v_{θ l}` for any
`θ : Fin (m+1) → Fin (m'+1)` (cofaces, codegeneracies and the horn retractions), and functoriality. -/

variable {m m' r : ℕ}

end PullS

section HornExt

/-! Horn filling for forms at the level of representatives (Lemma 5.9, surjectivity): the classical
inductive extension, correcting face by face with pullbacks along the retraction `retr i j` of
`Δᵐ⁺¹` onto its `i`-th face that moves the vertex `i` to the vertex `j`. -/

variable {m r : ℕ}

open Classical in
/-- The vertex map of the retraction onto the face `i` collapsing the vertex `i` onto `j`. -/
noncomputable def retr (i j : Fin (m + 2)) (k : Fin (m + 2)) : Fin (m + 1) :=
  if h : ∃ l, i.succAbove l = (if k = i then j else k) then h.choose else 0

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

end Fold


section ClosedGraph

/-! Continuity of the face maps and of the horn section by the closed graph theorem: limits in the
jet space control the coefficients pointwise (order-0 jet components), and pullbacks / folds
preserve pointwise convergence of coefficients. -/

variable {m r : ℕ}

/-- Pointwise convergence of all coefficients on the simplex. -/
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

end ClosedGraph


section HornSection

/-! The continuous linear horn section `E` (fold of retraction pullbacks on representatives),
the simplicial identities for `faceCr`, and Lemma 5.9 for `Ωⁿ_{Cʳ}`. -/

variable {m r : ℕ}

open Classical in
noncomputable def rep (n : ℕ) (j : Fin (m + 2))
    (y : {i : Fin (m + 2) // i ≠ j} → CrForms r m n) (i : Fin (m + 2)) : Ω m :=
  if hi : i ≠ j then
    (if h : ∃ ω : Ω m, (IsDeg n ω ∧ IsCr r ω) ∧ jet r ω = y ⟨i, hi⟩ then h.choose else 0)
  else 0

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

/-! a83e3b53 relay 8: regularity of the cone integral `x ↦ ∫₀¹ tᵖ • f (t • x) dt` within a compact
convex set containing `0` (the analytic core of the Poincare homotopy operator on the simplex). -/

set_option autoImplicit false

namespace IntLInfty.Kan.A83Cone

open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cone integral `x ↦ ∫₀¹ tᵖ • f (t • x) dt`. -/
noncomputable def coneInt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) (f : E → F)
    (x : E) : F :=
  ∫ t in (0 : ℝ)..1, (t ^ p) • f (t • x)

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

/-- Euler identity along rays: `(p+1) • K_p f x + (K_{p+1} f' x) x = f x`
(fundamental theorem of calculus for `t ↦ t^(p+1) • f (t • x)`). -/
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

/-! a83e3b53 relay 9: the Poincare identity `d (K β) = β` for the cone homotopy operator
`K β x = ι_x (∫₀¹ tⁿ β (t x) dt)` on closed `(n+1)`-forms, coordinate free (interior product =
`CliffordAlgebra.contractLeft`). The exterior algebra gets the norm transported from its basis. -/

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

section generic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

end generic

/-! ### The cone operator on forms of the simplex (relay 9, part 1b) -/

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

end IntLInfty.Kan.A83Poinc

/-! ## Part 2 (relay 10): rep-level horn filling with prescribed exterior derivative
(Lemma 5.11 surjectivity / the fibrewise filling step of K1): a horn of `n`-forms `αᵢ` and a closed
`(n+1)`-form `β` on `Δᵐ⁺¹` with `dαᵢ = dᵢ β` extend to an `n`-form `ω` with `dᵢ ω = αᵢ`, `dω = β`.
Construction: `ω = K β + γ`, `γ` a closed filler of the closed horn `αᵢ - dᵢ (K β)`. -/

namespace IntLInfty.Kan.A83Fill

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc

variable {m r : ℕ}

end IntLInfty.Kan.A83Fill

/-! ## Part 3 (relay 10): graphs of smooth maps are split submanifolds (tool for K0b).
`M = {x | x = P x + g x}` for a continuous idempotent `P` and a `C^∞` map `g` with `g ∘ P = g`,
`P ∘ g = 0`: the global chart `x ↦ x - g x` (inverse `y ↦ y + g y`) carries `M` onto `range P`. -/

namespace IntLInfty.Kan.A83Graph

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The global chart. -/
noncomputable def chart (g : E → E) (hg : Continuous g) (hgP : ∀ x, g (x - g x) = g x)
    (hgP' : ∀ y, g (y + g y) = g y) : E ≃ₜ E where
  toFun x := x - g x
  invFun y := y + g y
  left_inv x := by simp [hgP x]
  right_inv y := by simp [hgP' y]
  continuous_toFun := continuous_id.sub hg
  continuous_invFun := continuous_id.add hg

end IntLInfty.Kan.A83Graph

namespace IntLInfty.Kan.A83Graph

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end IntLInfty.Kan.A83Graph

/-! ## Relay 12: `CrClosed` is complemented in `CrForms`. The projection is `w ↦ w - jet (K (d ω))`
for any representative `ω` of `w`, where `K` is the cone (Poincaré) operator. -/

namespace IntLInfty.Kan.A83Proj

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

end IntLInfty.Kan.A83Proj

/-! ## Relay 12 (b): graded Leibniz rule for `extD` and `Cʳ` products (step (3) groundwork). -/

namespace IntLInfty.Kan.A83Leib

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc

attribute [local instance] algNAG algNS algFD algComplete

variable {m : ℕ}

/-- Graded commutativity of a degree-one element with a homogeneous element. -/
theorem iota_mul_comm {V : Type} [AddCommGroup V] [Module ℝ V] (v : V) :
    ∀ (p : ℕ) (a : ExteriorAlgebra ℝ V), a ∈ ⋀[ℝ]^p V →
      ExteriorAlgebra.ι ℝ v * a = (-1 : ℝ) ^ p • (a * ExteriorAlgebra.ι ℝ v)
  | 0, a, ha => by
    have ha' : a ∈ (LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V)) ^ 0 := ha
    rw [pow_zero, Submodule.mem_one] at ha'
    obtain ⟨c, rfl⟩ := ha'
    rw [pow_zero, one_smul]
    exact (Algebra.commutes c _).symm
  | p + 1, a, ha => by
    have ha' : a ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V) *
        (LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V)) ^ p := by
      rw [← pow_succ']; exact ha
    refine Submodule.mul_induction_on ha' (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · obtain ⟨u, rfl⟩ := hx
      have ih := iota_mul_comm v p y hy
      calc ExteriorAlgebra.ι ℝ v * (ExteriorAlgebra.ι ℝ u * y)
          = -(ExteriorAlgebra.ι ℝ u * (ExteriorAlgebra.ι ℝ v * y)) := by
            have hs : ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.ι ℝ u =
                -(ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v) :=
              eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v u)
            rw [← mul_assoc, hs, neg_mul, mul_assoc]
        _ = (-1 : ℝ) ^ (p + 1) • (ExteriorAlgebra.ι ℝ u * y * ExteriorAlgebra.ι ℝ v) := by
            rw [ih, mul_smul_comm, ← mul_assoc, pow_succ, mul_smul, neg_one_smul, smul_neg]
    · rw [mul_add, hx, hy, add_mul, smul_add]

/-- Multiplication of the exterior algebra as a continuous bilinear map. -/
noncomputable def mulB (m : ℕ) : Alg m →L[ℝ] Alg m →L[ℝ] Alg m :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Alg m →ₗ[ℝ] Alg m) ≃ₗ[ℝ] (Alg m →L[ℝ] Alg m)).toLinearMap ∘ₗ
      LinearMap.mul ℝ (Alg m))

theorem mulB_apply (m : ℕ) (a b : Alg m) : mulB m a b = a * b := by
  simp [mulB]

theorem mul_eq_mulB (γ η : Ω m) : γ * η = fun y => mulB m (γ y) (η y) := by
  funext y
  simp [mulB_apply]

theorem coeff_contDiffOn_of {r : ℕ} {α : Ω m} (h : ContDiffOn ℝ r α (simplex m))
    (I : Finset (Fin m)) : ContDiffOn ℝ r (coeff α I) (simplex m) := by
  rw [coeff_eq_coeffL]
  exact (coeffL m I).contDiff.comp_contDiffOn h

/-- Graded Leibniz rule on the simplex: `d(α ∧ β) = dα ∧ β + (-1)^p α ∧ dβ` for a `p`-form `α`. -/
theorem extD_mul {r p : ℕ} (hr : 1 ≤ r) {α β : Ω m} (hα : IsCr r α) (hβ : IsCr r β)
    (hD : IsDeg p α) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    extD (α * β) x = extD α x * β x + (-1 : ℝ) ^ p • (α x * extD β x) := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hda : DifferentiableWithinAt ℝ α (simplex m) x :=
    ((contDiffOn_of_coeff fun I => (hα I).1).differentiableOn hr0) x hx
  have hdb : DifferentiableWithinAt ℝ β (simplex m) x :=
    ((contDiffOn_of_coeff fun I => (hβ I).1).differentiableOn hr0) x hx
  have hD2 := (mulB m).hasFDerivWithinAt_of_bilinear hda.hasFDerivWithinAt hdb.hasFDerivWithinAt
  have hdab : DifferentiableWithinAt ℝ (α * β) (simplex m) x := by
    rw [mul_eq_mulB]; exact hD2.differentiableWithinAt
  have hU := A83.uniqueDiffOn_simplex m x hx
  have hval : ∀ v, fderivWithin ℝ (α * β) (simplex m) x v =
      fderivWithin ℝ α (simplex m) x v * β x + α x * fderivWithin ℝ β (simplex m) x v := by
    intro v
    rw [mul_eq_mulB, hD2.fderivWithin hU]
    simp [mulB_apply, add_comm]
  rw [extD_eq_fderiv hx hdab, extD_eq_fderiv hx hda, extD_eq_fderiv hx hdb]
  simp only [hval, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : dx m k * α x = (-1 : ℝ) ^ p • (α x * dx m k) := iota_mul_comm _ p _ (hD x hx)
  rw [← mul_assoc, hc, smul_mul_assoc, mul_assoc]

/-- Products of `Cʳ` forms (with `Cʳ` differential) are `Cʳ` with `Cʳ` differential. -/
theorem isCr_mul {r p : ℕ} (hr : 1 ≤ r) {α β : Ω m} (hα : IsCr r α) (hβ : IsCr r β)
    (hD : IsDeg p α) : IsCr r (α * β) := by
  have cα := contDiffOn_of_coeff fun I => (hα I).1
  have cβ := contDiffOn_of_coeff fun I => (hβ I).1
  have cdα := contDiffOn_of_coeff fun I => (hα I).2
  have cdβ := contDiffOn_of_coeff fun I => (hβ I).2
  have hB := (mulB m).isBoundedBilinearMap.contDiff (n := (r : WithTop ℕ∞))
  intro I
  constructor
  · apply coeff_contDiffOn_of
    rw [mul_eq_mulB]
    exact hB.comp_contDiffOn (cα.prodMk cβ)
  · have e1 := hB.comp_contDiffOn (cdα.prodMk cβ)
    have e2 := hB.comp_contDiffOn (cα.prodMk cdβ)
    have h1 : ContDiffOn ℝ r (fun y => extD α y * β y + (-1 : ℝ) ^ p • (α y * extD β y))
        (simplex m) := by
      have := e1.add (e2.const_smul ((-1 : ℝ) ^ p))
      simpa [mulB_apply, Function.comp_def] using this
    have h2 := coeff_contDiffOn_of h1 I
    refine h2.congr fun y hy => ?_
    simp only [coeff]
    rw [extD_mul hr hα hβ hD hy]

theorem isDeg_mul {p q : ℕ} {α β : Ω m} (hα : IsDeg p α) (hβ : IsDeg q β) :
    IsDeg (p + q) (α * β) := fun x hx => by
  show α x * β x ∈ LinearMap.range (ExteriorAlgebra.ι ℝ :
    Module.Dual ℝ (Fin m → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) ^ (p + q)
  rw [pow_add]
  exact Submodule.mul_mem_mul (hα x hx) (hβ x hx)

end IntLInfty.Kan.A83Leib


namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan

section Ext

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem iota_mul_comm' (v : V) :
    ∀ (p : ℕ) (a : ExteriorAlgebra ℝ V), a ∈ ⋀[ℝ]^p V →
      ExteriorAlgebra.ι ℝ v * a = (-1 : ℝ) ^ p • (a * ExteriorAlgebra.ι ℝ v)
  | 0, a, ha => by
    have ha' : a ∈ (LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V)) ^ 0 := ha
    rw [pow_zero, Submodule.mem_one] at ha'
    obtain ⟨c, rfl⟩ := ha'
    rw [pow_zero, one_smul]
    exact (Algebra.commutes c _).symm
  | p + 1, a, ha => by
    have ha' : a ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V) *
        (LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V)) ^ p := by
      rw [← pow_succ']; exact ha
    refine Submodule.mul_induction_on ha' (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · obtain ⟨u, rfl⟩ := hx
      have ih := iota_mul_comm' v p y hy
      calc ExteriorAlgebra.ι ℝ v * (ExteriorAlgebra.ι ℝ u * y)
          = -(ExteriorAlgebra.ι ℝ u * (ExteriorAlgebra.ι ℝ v * y)) := by
            have hs : ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.ι ℝ u =
                -(ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v) :=
              eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v u)
            rw [← mul_assoc, hs, neg_mul, mul_assoc]
        _ = (-1 : ℝ) ^ (p + 1) • (ExteriorAlgebra.ι ℝ u * y * ExteriorAlgebra.ι ℝ v) := by
            rw [ih, mul_smul_comm, ← mul_assoc, pow_succ, mul_smul, neg_one_smul, smul_neg]
    · rw [mul_add, hx, hy, add_mul, smul_add]

/-- Graded commutativity: `b a = (-1)^{pq} a b` for `a ∈ ⋀^p`, `b ∈ ⋀^q`. -/
theorem mul_comm_graded (p : ℕ) (a : ExteriorAlgebra ℝ V) (ha : a ∈ ⋀[ℝ]^p V) :
    ∀ (q : ℕ) (b : ExteriorAlgebra ℝ V), b ∈ ⋀[ℝ]^q V → b * a = (-1 : ℝ) ^ (p * q) • (a * b)
  | 0, b, hb => by
    have hb' : b ∈ (LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V)) ^ 0 := hb
    rw [pow_zero, Submodule.mem_one] at hb'
    obtain ⟨c, rfl⟩ := hb'
    rw [mul_zero, pow_zero, one_smul]
    exact Algebra.commutes c a
  | q + 1, b, hb => by
    have hb' : b ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V) *
        (LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V)) ^ q := by
      rw [← pow_succ']; exact hb
    refine Submodule.mul_induction_on hb' (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · obtain ⟨u, rfl⟩ := hx
      have ih := mul_comm_graded p a ha q y hy
      have hι := iota_mul_comm' u p a ha
      calc ExteriorAlgebra.ι ℝ u * y * a = ExteriorAlgebra.ι ℝ u * (y * a) := mul_assoc _ _ _
        _ = (-1 : ℝ) ^ (p * q) • ((ExteriorAlgebra.ι ℝ u * a) * y) := by
            rw [ih, mul_smul_comm, ← mul_assoc]
        _ = (-1 : ℝ) ^ (p * (q + 1)) • (a * (ExteriorAlgebra.ι ℝ u * y)) := by
            rw [hι, smul_mul_assoc, smul_smul, ← pow_add, mul_assoc]
            congr 2
    · rw [add_mul, hx, hy, ← smul_add, ← mul_add]

/-- Odd elements anticommute. -/
theorem anticomm_of_odd {p q : ℕ} (hp : Odd p) (hq : Odd q) {a b : ExteriorAlgebra ℝ V}
    (ha : a ∈ ⋀[ℝ]^p V) (hb : b ∈ ⋀[ℝ]^q V) : b * a = -(a * b) := by
  rw [mul_comm_graded p a ha q b hb, Odd.neg_one_pow (Nat.odd_mul.2 ⟨hp, hq⟩), neg_one_smul]

/-- An element of even degree commutes with everything. -/
theorem commute_of_even {q : ℕ} (hq : Even q) {b : ExteriorAlgebra ℝ V} (hb : b ∈ ⋀[ℝ]^q V)
    (a : ExteriorAlgebra ℝ V) : b * a = a * b := by
  induction a using ExteriorAlgebra.induction with
  | algebraMap c => exact (Algebra.commutes c b).symm
  | ι v =>
      rw [iota_mul_comm' v q b hb, Even.neg_one_pow hq, one_smul]
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  | add x y hx hy => rw [mul_add, hx, hy, add_mul]

end Ext

section Lift

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

/-- Hypothesis on generator values: each `f i ξ` is pointwise homogeneous of degree `i + 1`. -/
def GenHom (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) : Prop :=
  ∀ i ξ x, f i ξ x ∈ ⋀[ℝ]^(i + 1) (Module.Dual ℝ (Fin m → ℝ))

theorem mem_center_of_even {q : ℕ} (hq : Even q) {ω : Ω m}
    (hω : ∀ x, ω x ∈ ⋀[ℝ]^q (Module.Dual ℝ (Fin m → ℝ))) : ω ∈ Subalgebra.center ℝ (Ω m) := by
  rw [Subalgebra.mem_center_iff]
  intro g
  funext x
  exact (commute_of_even hq (hω x) (g x)).symm

/-- The exterior part: generators of even `i` (odd degree). -/
noncomputable def fE (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) :
    DirectSum {i : ℕ // Even i} (fun i => Module.Dual ℝ (L i.1)) →ₗ[ℝ] Ω m :=
  DirectSum.toModule ℝ {i : ℕ // Even i} (Ω m) (fun i => f i.1)

theorem fE_anticomm (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f)
    (v w : DirectSum {i : ℕ // Even i} (fun i => Module.Dual ℝ (L i.1))) :
    fE f w * fE f v = -(fE f v * fE f w) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i ξ =>
    induction w using DirectSum.induction_on with
    | zero => simp
    | of j η =>
      have e1 : fE f (DirectSum.of _ i ξ) = f i.1 ξ := by
        rw [fE, ← DirectSum.lof_eq_of ℝ, DirectSum.toModule_lof]
      have e2 : fE f (DirectSum.of _ j η) = f j.1 η := by
        rw [fE, ← DirectSum.lof_eq_of ℝ, DirectSum.toModule_lof]
      rw [e1, e2]
      funext x
      simp only [Pi.mul_apply, Pi.neg_apply]
      exact anticomm_of_odd (Even.add_one i.2) (Even.add_one j.2) (hf i.1 ξ x) (hf j.1 η x)
    | add w w' hw hw' => simp only [map_add, add_mul, mul_add, hw, hw', neg_add]
  | add v v' hv hv' => simp only [map_add, add_mul, mul_add, hv, hv', neg_add]

theorem fE_sq (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f)
    (v : DirectSum {i : ℕ // Even i} (fun i => Module.Dual ℝ (L i.1))) :
    fE f v * fE f v = 0 := by
  have h := fE_anticomm f hf v v
  have h2 : (2 : ℝ) • (fE f v * fE f v) = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- Generators of odd `i` (even degree) land in the center. -/
noncomputable def fSi (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) (i : {i : ℕ // Odd i}) :
    Module.Dual ℝ (L i.1) →ₗ[ℝ] Subalgebra.center ℝ (Ω m) where
  toFun ξ := ⟨f i.1 ξ, mem_center_of_even (Odd.add_one i.2) (hf i.1 ξ)⟩
  map_add' ξ η := Subtype.ext (map_add (f i.1) ξ η)
  map_smul' c ξ := Subtype.ext (map_smul (f i.1) c ξ)

noncomputable def fS (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) :
    DirectSum {i : ℕ // Odd i} (fun i => Module.Dual ℝ (L i.1)) →ₗ[ℝ] Subalgebra.center ℝ (Ω m) :=
  DirectSum.toModule ℝ {i : ℕ // Odd i} _ (fSi f hf)

/-- The algebra map `C∗(L) → Ω∗` determined by generator values. -/
noncomputable def ceLift (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) :
    CE L →ₐ[ℝ] Ω m :=
  Algebra.TensorProduct.lift (ExteriorAlgebra.lift ℝ ⟨fE f, fE_sq f hf⟩)
    ((Subalgebra.center ℝ (Ω m)).val.comp (SymmetricAlgebra.lift (fS f hf)))
    (fun x y => by
      have hy := ((SymmetricAlgebra.lift (fS f hf)) y).2
      rw [Subalgebra.mem_center_iff] at hy
      exact hy _)

end Lift

end IntLInfty.Kan.A83DGA

/-! Relay 13: the DGA condition for `ceLift` reduces to generators (step 3b part 2). -/

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83Proj

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem one_mem_ceDeg : (1 : CE L) ∈ ceDeg L 0 :=
  Submodule.subset_span ⟨0, Fin.elim0, fun t => Fin.elim0 t, by simp, by simp⟩

theorem gen_mem_ceDeg (i : ℕ) (ξ : Module.Dual ℝ (L i)) : gen L i ξ ∈ ceDeg L (i + 1) :=
  Submodule.subset_span ⟨1, fun _ => i, fun _ => ξ, by simp, by simp⟩

theorem delta_one (δ : LInfty L) : δ.δ 1 = 0 := by
  have h := δ.leibniz 0 1 one_mem_ceDeg 1
  rw [one_mul, pow_zero, one_smul, one_mul, mul_one] at h
  have h' : δ.δ 1 + δ.δ 1 = δ.δ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

end IntLInfty.Kan.A83DGA

/-! Relay 13: uniqueness on `A_S` and normalisation of generator values (cut off the simplex). -/

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83DGA

/-! ## (3c) δ-closure of the Postnikov generator algebras: `genAlg (tauLt n)` -/

namespace IntLInfty.Kan.A83Tau

open IntLInfty.Kan IntLInfty.Kan.A83

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83Tau

/-! ## (3c) detection homomorphisms: freeness facts about `C∗(L)` needed for the `τ≤n` half -/

namespace IntLInfty.Kan.A83Det

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

section Lift

variable {A : Type} [Ring A] [Algebra ℝ A]

end Lift

/-! ### odd top index: target `Polynomial (DualNumber ℝ)` -/

section OddTop

end OddTop

/-! ### even top index: target `ExteriorAlgebra ℝ (Fin 2 → ℝ)` -/

section EvenTop

end EvenTop

end IntLInfty.Kan.A83Det

/-! ## (3c) second half: `genAlg (tauLe n)` is `δ`-closed -/

namespace IntLInfty.Kan.A83TauLe

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Tau
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83TauLe


namespace IntLInfty.Kan.A83Wedge

/-! Relay 16: the wedge product on `Ω_{Cʳ}` is a continuous bilinear map
`CrForms r m p × CrForms r m q → CrForms r m (p + q)` (closed graph in each variable, then closed
graph for the outer map into the operator space), hence `C^∞`. -/

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib Filter Topology
open scoped ContDiff

variable {m r : ℕ}

theorem coeff_mul (α β : Ω m) (I : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (α * β) I x = ∑ J, ∑ K, coeff α J x * coeff β K x *
      (formBasis m).repr (formBasis m J * formBasis m K) I := by
  have e : (α * β) x = α x * β x := rfl
  simp only [coeff, e]
  conv_lhs => rw [← (formBasis m).sum_repr (α x), ← (formBasis m).sum_repr (β x)]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_comm

theorem coeffTendsto_mul_left (α : Ω m) {βk : ℕ → Ω m} {β : Ω m} (h : CoeffTendsto βk β) :
    CoeffTendsto (fun k => α * βk k) (α * β) := by
  intro I x hx
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun J _ => tendsto_finsetSum _ fun K _ =>
    (tendsto_const_nhds.mul (h K x hx)).mul_const _

theorem coeffTendsto_mul_right {αk : ℕ → Ω m} {α : Ω m} (β : Ω m) (h : CoeffTendsto αk α) :
    CoeffTendsto (fun k => αk k * β) (α * β) := by
  intro I x hx
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun J _ => tendsto_finsetSum _ fun K _ =>
    ((h J x hx).mul tendsto_const_nhds).mul_const _

theorem formEqOn_mul {α α' β β' : Ω m} (h1 : FormEqOn α α') (h2 : FormEqOn β β') :
    FormEqOn (α * β) (α' * β') := fun x hx => by
  show α x * β x = α' x * β' x
  rw [h1 x hx, h2 x hx]

/-- A chosen representative form of a point of `Ωⁿ_{Cʳ}(Δᵐ)`. -/
noncomputable def wRep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) : Ω m :=
  (exists_rep hr w).choose

theorem wRep_spec (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    (IsDeg n (wRep hr w) ∧ IsCr r (wRep hr w)) ∧ jet r (wRep hr w) = w :=
  (exists_rep hr w).choose_spec

theorem wedge_mem (hr : 1 ≤ r) {p q : ℕ} {α β : Ω m} (hα : IsDeg p α ∧ IsCr r α)
    (hβ : IsDeg q β ∧ IsCr r β) : jet r (α * β) ∈ CrForms r m (p + q) := by
  rw [← SetLike.mem_coe, crForms_eq_image hr (p + q)]
  exact ⟨_, ⟨isDeg_mul hα.1 hβ.1, isCr_mul hr hα.2 hβ.2 hα.1⟩, rfl⟩

noncomputable def wedgeFun (hr : 1 ≤ r) {p q : ℕ} (w1 : CrForms r m p) (w2 : CrForms r m q) :
    CrForms r m (p + q) :=
  ⟨jet r (wRep hr w1 * wRep hr w2), wedge_mem hr (wRep_spec hr w1).1 (wRep_spec hr w2).1⟩

theorem wedgeFun_val (hr : 1 ≤ r) {p q : ℕ} {w1 : CrForms r m p} {w2 : CrForms r m q}
    {α β : Ω m} (hα : IsDeg p α ∧ IsCr r α) (hβ : IsDeg q β ∧ IsCr r β)
    (h1 : jet r α = w1) (h2 : jet r β = w2) :
    (wedgeFun hr w1 w2 : Jet r m × Jet r m) = jet r (α * β) :=
  jet_congr (formEqOn_mul
    (formEqOn_of_jet (wRep_spec hr w1).1.2 hα.2 ((wRep_spec hr w1).2.trans h1.symm))
    (formEqOn_of_jet (wRep_spec hr w2).1.2 hβ.2 ((wRep_spec hr w2).2.trans h2.symm)))

/-- The wedge product as a bilinear map. -/
noncomputable def wedgeL (hr : 1 ≤ r) (p q : ℕ) :
    CrForms r m p →ₗ[ℝ] CrForms r m q →ₗ[ℝ] CrForms r m (p + q) :=
  LinearMap.mk₂ ℝ (wedgeFun hr)
    (fun a a' b => by
      obtain ⟨hα, eα⟩ := wRep_spec hr a
      obtain ⟨hα', eα'⟩ := wRep_spec hr a'
      obtain ⟨hβ, eβ⟩ := wRep_spec hr b
      apply Subtype.ext
      rw [Submodule.coe_add, wedgeFun_val hr hα hβ eα eβ, wedgeFun_val hr hα' hβ eα' eβ,
        wedgeFun_val hr ⟨isDeg_add hα.1 hα'.1, isCr_add hr hα.2 hα'.2⟩ hβ
          (by rw [jet_add hr hα.2 hα'.2, eα, eα']; rfl) eβ, add_mul,
        jet_add hr (isCr_mul hr hα.2 hβ.2 hα.1) (isCr_mul hr hα'.2 hβ.2 hα'.1)])
    (fun c a b => by
      obtain ⟨hα, eα⟩ := wRep_spec hr a
      obtain ⟨hβ, eβ⟩ := wRep_spec hr b
      apply Subtype.ext
      rw [Submodule.coe_smul, wedgeFun_val hr hα hβ eα eβ,
        wedgeFun_val hr ⟨isDeg_smul c hα.1, isCr_smul hr c hα.2⟩ hβ
          (by rw [jet_smul hr c hα.2, eα]; rfl) eβ, smul_mul_assoc,
        jet_smul hr c (isCr_mul hr hα.2 hβ.2 hα.1)])
    (fun a b b' => by
      obtain ⟨hα, eα⟩ := wRep_spec hr a
      obtain ⟨hβ, eβ⟩ := wRep_spec hr b
      obtain ⟨hβ', eβ'⟩ := wRep_spec hr b'
      apply Subtype.ext
      rw [Submodule.coe_add, wedgeFun_val hr hα hβ eα eβ, wedgeFun_val hr hα hβ' eα eβ',
        wedgeFun_val hr hα ⟨isDeg_add hβ.1 hβ'.1, isCr_add hr hβ.2 hβ'.2⟩ eα
          (by rw [jet_add hr hβ.2 hβ'.2, eβ, eβ']; rfl), mul_add,
        jet_add hr (isCr_mul hr hα.2 hβ.2 hα.1) (isCr_mul hr hα.2 hβ'.2 hα.1)])
    (fun c a b => by
      obtain ⟨hα, eα⟩ := wRep_spec hr a
      obtain ⟨hβ, eβ⟩ := wRep_spec hr b
      apply Subtype.ext
      rw [Submodule.coe_smul, wedgeFun_val hr hα hβ eα eβ,
        wedgeFun_val hr hα ⟨isDeg_smul c hβ.1, isCr_smul hr c hβ.2⟩ eα
          (by rw [jet_smul hr c hβ.2, eβ]; rfl), mul_smul_comm,
        jet_smul hr c (isCr_mul hr hα.2 hβ.2 hα.1)])

theorem wedgeL_val (hr : 1 ≤ r) {p q : ℕ} {w1 : CrForms r m p} {w2 : CrForms r m q}
    {α β : Ω m} (hα : IsDeg p α ∧ IsCr r α) (hβ : IsDeg q β ∧ IsCr r β)
    (h1 : jet r α = w1) (h2 : jet r β = w2) :
    (wedgeL hr p q w1 w2 : Jet r m × Jet r m) = jet r (α * β) :=
  wedgeFun_val hr hα hβ h1 h2

theorem wedge_cont_right (hr : 1 ≤ r) (p q : ℕ) (a : CrForms r m p) :
    Continuous (wedgeL hr p q a) := by
  have := crForms_complete r m q
  have := crForms_complete r m (p + q)
  refine (wedgeL hr p q a).continuous_of_seq_closed_graph fun u w z hu hz => ?_
  obtain ⟨hα, eα⟩ := wRep_spec hr a
  choose βk hβk ek using fun k => exists_rep hr (u k)
  obtain ⟨β, hβ, eβ⟩ := exists_rep hr w
  obtain ⟨ωz, hωz, ez⟩ := exists_rep hr z
  have hval : ∀ k, (wedgeL hr p q a (u k) : Jet r m × Jet r m) = jet r (wRep hr a * βk k) :=
    fun k => wedgeL_val hr hα (hβk k) eα (ek k)
  have t1 : CoeffTendsto (fun k => wRep hr a * βk k) ωz := by
    refine coeffTendsto_of_jet (fun k => isCr_mul hr hα.2 (hβk k).2 hα.1) hωz.2 ?_
    have := (continuous_subtype_val.tendsto z).comp hz
    rw [ez]
    exact this.congr fun k => hval k
  have t2 : CoeffTendsto (fun k => wRep hr a * βk k) (wRep hr a * β) := by
    refine coeffTendsto_mul_left _ (coeffTendsto_of_jet (fun k => (hβk k).2) hβ.2 ?_)
    have := (continuous_subtype_val.tendsto w).comp hu
    rw [eβ]
    exact this.congr fun k => (ek k).symm
  apply Subtype.ext
  show (z : Jet r m × Jet r m) = (wedgeL hr p q a w : Jet r m × Jet r m)
  rw [wedgeL_val hr hα hβ eα eβ, ← ez]
  exact jet_congr (coeffTendsto_unique t1 t2)

theorem wedge_cont_left (hr : 1 ≤ r) (p q : ℕ) (b : CrForms r m q) :
    Continuous ((wedgeL hr p q).flip b) := by
  have := crForms_complete r m p
  have := crForms_complete r m (p + q)
  set g := (wedgeL hr p q).flip b with hgdef
  have hg : ∀ a, g a = wedgeL hr p q a b := fun a => LinearMap.flip_apply _ _ _
  refine g.continuous_of_seq_closed_graph fun u w z hu hz => ?_
  obtain ⟨hβ, eβ⟩ := wRep_spec hr b
  choose αk hαk ek using fun k => exists_rep hr (u k)
  obtain ⟨α, hα, eα⟩ := exists_rep hr w
  obtain ⟨ωz, hωz, ez⟩ := exists_rep hr z
  have hval : ∀ k, ((g ∘ u) k : Jet r m × Jet r m) = jet r (αk k * wRep hr b) := by
    intro k
    rw [Function.comp_apply, hg]
    exact wedgeL_val hr (hαk k) hβ (ek k) eβ
  have t1 : CoeffTendsto (fun k => αk k * wRep hr b) ωz := by
    refine coeffTendsto_of_jet (fun k => isCr_mul hr (hαk k).2 hβ.2 (hαk k).1) hωz.2 ?_
    have := (continuous_subtype_val.tendsto z).comp hz
    rw [ez]
    exact this.congr fun k => hval k
  have t2 : CoeffTendsto (fun k => αk k * wRep hr b) (α * wRep hr b) := by
    refine coeffTendsto_mul_right _ (coeffTendsto_of_jet (fun k => (hαk k).2) hα.2 ?_)
    have := (continuous_subtype_val.tendsto w).comp hu
    rw [eα]
    exact this.congr fun k => (ek k).symm
  rw [hg]
  apply Subtype.ext
  rw [wedgeL_val hr hα hβ eα eβ, ← ez]
  exact jet_congr (coeffTendsto_unique t1 t2)

/-- The wedge product into the operator space. -/
noncomputable def wedgeR (hr : 1 ≤ r) (p q : ℕ) :
    CrForms r m p →ₗ[ℝ] (CrForms r m q →L[ℝ] CrForms r m (p + q)) where
  toFun a := ⟨wedgeL hr p q a, wedge_cont_right hr p q a⟩
  map_add' a a' := by
    ext1 b
    exact LinearMap.congr_fun ((wedgeL hr p q).map_add a a') b
  map_smul' c a := by
    ext1 b
    exact LinearMap.congr_fun ((wedgeL hr p q).map_smul c a) b

theorem wedgeR_continuous (hr : 1 ≤ r) (p q : ℕ) : Continuous (wedgeR (m := m) hr p q) := by
  have := crForms_complete r m p
  have := crForms_complete r m (p + q)
  refine LinearMap.continuous_of_seq_closed_graph (𝕜 := ℝ)
    (E := CrForms r m p) (F := CrForms r m q →L[ℝ] CrForms r m (p + q))
    (g := wedgeR (m := m) hr p q) fun u a Z hu hZ => ?_
  ext1 b
  have h1 : Tendsto (fun k => wedgeR hr p q (u k) b) atTop (𝓝 (Z b)) :=
    ((ContinuousLinearMap.apply ℝ (CrForms r m (p + q)) b).continuous.tendsto Z).comp hZ
  have h2 : Tendsto (fun k => wedgeR hr p q (u k) b) atTop (𝓝 (wedgeR hr p q a b)) :=
    ((wedge_cont_left hr p q b).tendsto a).comp hu
  exact tendsto_nhds_unique h1 h2

/-- The wedge product `Ωᵖ_{Cʳ}(Δᵐ) × Ω^q_{Cʳ}(Δᵐ) → Ω^{p+q}_{Cʳ}(Δᵐ)` as a continuous bilinear map. -/
noncomputable def wedgeCLM (hr : 1 ≤ r) (p q : ℕ) :
    CrForms r m p →L[ℝ] CrForms r m q →L[ℝ] CrForms r m (p + q) :=
  ⟨wedgeR hr p q, wedgeR_continuous hr p q⟩

theorem wedgeCLM_val (hr : 1 ≤ r) {p q : ℕ} {w1 : CrForms r m p} {w2 : CrForms r m q}
    {α β : Ω m} (hα : IsDeg p α ∧ IsCr r α) (hβ : IsDeg q β ∧ IsCr r β)
    (h1 : jet r α = w1) (h2 : jet r β = w2) :
    (wedgeCLM hr p q w1 w2 : Jet r m × Jet r m) = jet r (α * β) :=
  wedgeFun_val hr hα hβ h1 h2

/-- (3) jet wedge smoothness: the wedge product on `Ω_{Cʳ}` is `C^∞`. -/
theorem contDiff_wedge (hr : 1 ≤ r) (p q : ℕ) :
    ContDiff ℝ ∞ (fun x : CrForms r m p × CrForms r m q => wedgeCLM hr p q x.1 x.2) :=
  (wedgeCLM hr p q).isBoundedBilinearMap.contDiff

end IntLInfty.Kan.A83Wedge

/-! ## Relay 17: cone Gronwall (Volterra uniqueness along rays). If `‖B x‖ ≤ C ‖x‖ ∫₀¹ ‖B (t x)‖ dt`
on a star-shaped set and `B` is bounded and continuous there, then `B = 0`. This is the uniqueness
step for the K0b characterization `H z = K N(z) ↔ d z = N(z)` (the defect `B = dz - N z` satisfies
`B = K (linear in B)` by `δ² = 0`). -/

namespace IntLInfty.Kan.A83Gron

open intervalIntegral

theorem cone_gronwall {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] {S : Set E}
    (hstar : ∀ x ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ S) (B : E → F)
    (hB : ContinuousOn B S) {M : ℝ} (hM : ∀ x ∈ S, ‖B x‖ ≤ M) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ S, ‖B x‖ ≤ C * ‖x‖ * ∫ t in (0 : ℝ)..1, ‖B (t • x)‖) :
    ∀ x ∈ S, B x = 0 := by
  -- integrability of `t ↦ ‖B (t • x)‖` on `[0,1]`
  have hint : ∀ x ∈ S, IntervalIntegrable (fun t : ℝ => ‖B (t • x)‖) MeasureTheory.volume 0 1 := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    refine (hB.comp (continuous_id.smul continuous_const).continuousOn ?_).norm
    intro t ht
    exact hstar x hx t ht
  have key : ∀ k : ℕ, ∀ x ∈ S, ‖B x‖ ≤ M * (C * ‖x‖) ^ k / k.factorial := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hM x hx
    | succ k ih =>
      intro x hx
      have hle : (∫ t in (0 : ℝ)..1, ‖B (t • x)‖) ≤
          ∫ t in (0 : ℝ)..1, M * (C * ‖x‖) ^ k / k.factorial * t ^ k := by
        apply intervalIntegral.integral_mono_on zero_le_one (hint x hx)
        · exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
        · intro t ht
          have h1 := ih (t • x) (hstar x hx t ht)
          rw [norm_smul, Real.norm_of_nonneg ht.1] at h1
          calc ‖B (t • x)‖ ≤ M * (C * (t * ‖x‖)) ^ k / k.factorial := h1
            _ = M * (C * ‖x‖) ^ k / k.factorial * t ^ k := by ring
      have hcalc : (∫ t in (0 : ℝ)..1, M * (C * ‖x‖) ^ k / k.factorial * t ^ k) =
          M * (C * ‖x‖) ^ k / k.factorial / (k + 1) := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp
        ring
      have hCx : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg x)
      calc ‖B x‖ ≤ C * ‖x‖ * ∫ t in (0 : ℝ)..1, ‖B (t • x)‖ := h x hx
        _ ≤ C * ‖x‖ * (M * (C * ‖x‖) ^ k / k.factorial / (k + 1)) := by
          rw [← hcalc]; exact mul_le_mul_of_nonneg_left hle hCx
        _ = M * (C * ‖x‖) ^ (k + 1) / (k + 1).factorial := by
          rw [Nat.factorial_succ]; push_cast; field_simp; ring
  intro x hx
  have hlim : Filter.Tendsto (fun k : ℕ => M * ((C * ‖x‖) ^ k / k.factorial)) Filter.atTop
      (nhds (M * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (C * ‖x‖)).const_mul M
  rw [mul_zero] at hlim
  have hle0 : ‖B x‖ ≤ 0 := by
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
    have := key k x hx
    rw [mul_div_assoc] at this
    exact this
  exact norm_le_zero_iff.mp hle0

end IntLInfty.Kan.A83Gron

open IntLInfty.Kan in
open scoped ContDiff in
theorem solution :
    (∀ {m r : ℕ}, 1 ≤ r → ∃ W : ∀ p q : ℕ, CrForms r m p →L[ℝ] CrForms r m q →L[ℝ] CrForms r m (p + q), (∀ (p q : ℕ) (w1 : CrForms r m p) (w2 : CrForms r m q) (α β : Ω m), IsDeg p α ∧ IsCr r α → IsDeg q β ∧ IsCr r β → jet r α = w1 → jet r β = w2 → (W p q w1 w2 : Jet r m × Jet r m) = jet r (α * β)) ∧ ∀ p q : ℕ, ContDiff ℝ ∞ (fun x : CrForms r m p × CrForms r m q => W p q x.1 x.2)) ∧
    (∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] {S : Set E}, (∀ x ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ S) → ∀ B : E → F, ContinuousOn B S → ∀ {M : ℝ}, (∀ x ∈ S, ‖B x‖ ≤ M) → ∀ {C : ℝ}, 0 ≤ C → (∀ x ∈ S, ‖B x‖ ≤ C * ‖x‖ * ∫ t in (0 : ℝ)..1, ‖B (t • x)‖) → ∀ x ∈ S, B x = 0) := by
  refine ⟨fun {m r} hr => ⟨fun p q => A83Wedge.wedgeCLM hr p q,
    fun p q w1 w2 α β hα hβ h1 h2 => A83Wedge.wedgeCLM_val hr hα hβ h1 h2,
    fun p q => A83Wedge.contDiff_wedge hr p q⟩, ?_⟩
  intro E F _ _ _ S hstar B hB M hM C hC h
  exact A83Gron.cone_gronwall hstar B hB hM hC h
