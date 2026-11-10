-- Prove2me | solution 1 for IntLInfty.Kan.generator_lift_dga
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:48:11.659148+00:00
-- url     : https://prove2.me/submissions/029d631d-0c3e-40c0-b584-88bedb84087a

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

theorem isCr_zero : IsCr r (0 : Ω m) := by
  intro I
  have h0 : ∀ J, coeff (0 : Ω m) J = fun _ => 0 := by intro J; funext x; simp [coeff]
  have h1 : extD (0 : Ω m) = 0 := by funext x; simp [extD, h0]
  refine ⟨by rw [h0]; exact contDiffOn_const, by rw [h1, h0]; exact contDiffOn_const⟩

end FormsLin2

open Filter Topology

section TaylorLimit

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

end TaylorLimit

section JetLimit

open IntLInfty.Kan BoundedContinuousFunction

end JetLimit

section JetClosed

open IntLInfty.Kan BoundedContinuousFunction

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

theorem extD_zero' (hr : 1 ≤ r) {x : Fin m → ℝ} (hx : x ∈ simplex m) : extD (0 : Ω m) x = 0 := by
  have := extD_smul hr (0 : ℝ) (isCr_zero (r := r) (m := m)) hx
  simpa using this

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

theorem ceLift_gen (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) : ceLift f hf (gen L i ξ) = f i ξ := by
  unfold gen
  by_cases h : Even i
  · rw [dif_pos h]
    simp [ceLift, Algebra.TensorProduct.lift_tmul, fE]
  · rw [dif_neg h]
    simp [ceLift, Algebra.TensorProduct.lift_tmul, fS, fSi]

end Lift

end IntLInfty.Kan.A83DGA

/-! Relay 13: the DGA condition for `ceLift` reduces to generators (step 3b part 2). -/

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83Proj

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem isCr_const (r : ℕ) (a : ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :
    IsCr r (fun _ => a : Ω m) ∧ extD (fun _ => a : Ω m) = 0 := by
  have h0 : ∀ J, coeff (fun _ => a : Ω m) J = fun _ => (formBasis m).repr a J := fun J => rfl
  have h1 : extD (fun _ => a : Ω m) = 0 := by funext x; simp [extD, h0]
  have h2 : ∀ J, coeff (0 : Ω m) J = fun _ => 0 := by intro J; funext x; simp [coeff]
  exact ⟨fun I => ⟨by rw [h0]; exact contDiffOn_const, by rw [h1, h2]; exact contDiffOn_const⟩, h1⟩

theorem one_mem_ceDeg : (1 : CE L) ∈ ceDeg L 0 :=
  Submodule.subset_span ⟨0, Fin.elim0, fun t => Fin.elim0 t, by simp, by simp⟩

theorem gen_mem_ceDeg (i : ℕ) (ξ : Module.Dual ℝ (L i)) : gen L i ξ ∈ ceDeg L (i + 1) :=
  Submodule.subset_span ⟨1, fun _ => i, fun _ => ξ, by simp, by simp⟩

theorem delta_one (δ : LInfty L) : δ.δ 1 = 0 := by
  have h := δ.leibniz 0 1 one_mem_ceDeg 1
  rw [one_mul, pow_zero, one_smul, one_mul, mul_one] at h
  have h' : δ.δ 1 + δ.δ 1 = δ.δ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

/-- Leibniz + linearity: if an algebra map `Φ : C∗(L) → Ω∗` commutes with `d` on the generators
of `S` (with `Cʳ` homogeneous values), it does so on all of `A_S`, and all values are `Cʳ`. -/
theorem dga_of_gen {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L) (Φ : CE L →ₐ[ℝ] Ω m)
    (hdeg : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsDeg (i + 1) (Φ (gen L i ξ)))
    (hcr : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsCr r (Φ (gen L i ξ)))
    (hd : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
      ∀ x ∈ simplex m, extD (Φ (gen L i ξ)) x = Φ (δ.δ (gen L i ξ)) x)
    (a : CE L) (ha : a ∈ genAlg L S) :
    IsCr r (Φ a) ∧ ∀ x ∈ simplex m, extD (Φ a) x = Φ (δ.δ a) x := by
  have hspan : a ∈ Submodule.span ℝ (Submonoid.closure
      (⋃ i, (gen L i : Module.Dual ℝ (L i) → CE L) '' (S i : Set (Module.Dual ℝ (L i)))) : Set (CE L)) := by
    rw [← Algebra.adjoin_eq_span]; exact ha
  clear ha
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ Submonoid.closure
        (⋃ i, (gen L i : Module.Dual ℝ (L i) → CE L) '' (S i : Set (Module.Dual ℝ (L i)))) := hy
    clear hy
    induction hy' using Submonoid.closure_induction_left with
    | one =>
      have hc := isCr_const (m := m) r 1
      refine ⟨by rw [map_one]; exact hc.1, fun x hx => ?_⟩
      rw [map_one, delta_one, map_zero]
      exact congrFun hc.2 x
    | mul_left g hg y _ ih =>
      obtain ⟨i, ξ, hξ, rfl⟩ := Set.mem_iUnion.1 hg
      refine ⟨by rw [map_mul]; exact isCr_mul hr (hcr i ξ hξ) ih.1 (hdeg i ξ hξ), fun x hx => ?_⟩
      rw [map_mul, extD_mul hr (hcr i ξ hξ) ih.1 (hdeg i ξ hξ) hx,
        δ.leibniz (i + 1) _ (gen_mem_ceDeg i ξ) y, map_add, map_smul, map_mul, map_mul,
        hd i ξ hξ x hx, ih.2 x hx]
      rfl
  | zero =>
    exact ⟨by rw [map_zero]; exact isCr_zero, fun x hx => by
      simp only [map_zero, Pi.zero_apply]; exact extD_zero' hr hx⟩
  | add y z _ _ hy hz =>
    refine ⟨by rw [map_add]; exact isCr_add hr hy.1 hz.1, fun x hx => ?_⟩
    rw [map_add, extD_add hr hy.1 hz.1 hx, map_add, map_add, hy.2 x hx, hz.2 x hx]
    rfl
  | smul c y _ hy =>
    refine ⟨by rw [map_smul]; exact isCr_smul hr c hy.1, fun x hx => ?_⟩
    rw [map_smul, extD_smul hr c hy.1 hx, map_smul, map_smul, hy.2 x hx]
    rfl

end IntLInfty.Kan.A83DGA

/-! Relay 13: uniqueness on `A_S` and normalisation of generator values (cut off the simplex). -/

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem isCr_of_formEqOn {r : ℕ} {ω ω' : Ω m} (h : FormEqOn ω ω') (hC : IsCr r ω) :
    IsCr r ω' := fun I =>
  ⟨(hC I).1.congr (fun x hx => (coeff_eqOn h I hx).symm),
    (hC I).2.congr (fun x hx => (coeff_eqOn (extD_congr h) I hx).symm)⟩

end IntLInfty.Kan.A83DGA

open IntLInfty.Kan in
theorem solution :
    (∀ {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)]
      (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m),
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)) (x : Fin m → ℝ),
        f i ξ x ∈ ⋀[ℝ]^(i + 1) (Module.Dual ℝ (Fin m → ℝ))) →
      ∃ Φ : CE L →ₐ[ℝ] Ω m, ∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), Φ (gen L i ξ) = f i ξ) ∧
    (∀ {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)], 1 ≤ r →
      ∀ (δ : LInfty L) (S : GenSys L) (Φ : CE L →ₐ[ℝ] Ω m),
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsDeg (i + 1) (Φ (gen L i ξ))) →
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsCr r (Φ (gen L i ξ))) →
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        ∀ x ∈ simplex m, extD (Φ (gen L i ξ)) x = Φ (δ.δ (gen L i ξ)) x) →
      ∀ a ∈ genAlg L S, IsCr r (Φ a) ∧ ∀ x ∈ simplex m, extD (Φ a) x = Φ (δ.δ a) x) ∧
    (∀ {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)], 1 ≤ r →
      ∀ (δ : LInfty L) (S : GenSys L) (Φ : CE L →ₐ[ℝ] Ω m),
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsDeg (i + 1) (Φ (gen L i ξ))) →
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → IsCr r (Φ (gen L i ξ))) →
      (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        ∀ x ∈ simplex m, extD (Φ (gen L i ξ)) x = Φ (δ.δ (gen L i ξ)) x) →
      IsDGAMap r δ S m (Φ.comp (genAlg L S).val)) ∧
    (∀ {m r p : ℕ}, 1 ≤ r → ∀ {α β : Ω m}, IsCr r α → IsCr r β → IsDeg p α →
      ∀ x ∈ simplex m, extD (α * β) x = extD α x * β x + (-1 : ℝ) ^ p • (α x * extD β x)) ∧
    (∀ {m r p : ℕ}, 1 ≤ r → ∀ {α β : Ω m}, IsCr r α → IsCr r β → IsDeg p α → IsCr r (α * β)) ∧
    (∀ {m p q : ℕ} {α β : Ω m}, IsDeg p α → IsDeg q β → IsDeg (p + q) (α * β)) ∧
    (∀ {m : ℕ} (r : ℕ) (a : ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))),
      IsCr r (fun _ => a : Ω m) ∧ extD (fun _ => a : Ω m) = 0) ∧
    (∀ {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)] (δ : LInfty L),
      δ.δ 1 = 0) ∧
    (∀ {m r : ℕ} {ω ω' : Ω m}, (∀ x ∈ simplex m, ω x = ω' x) → IsCr r ω → IsCr r ω') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m L _ _ f hf
    exact ⟨A83DGA.ceLift f hf, A83DGA.ceLift_gen f hf⟩
  · intro m r L _ _ hr δ S Φ hdeg hcr hd a ha
    exact A83DGA.dga_of_gen hr δ S Φ hdeg hcr hd a ha
  · intro m r L _ _ hr δ S Φ hdeg hcr hd
    have key := A83DGA.dga_of_gen hr δ S Φ hdeg hcr hd
    refine ⟨fun i ξ h => hdeg i ξ h, fun a => (key a.1 a.2).1, fun a b hab x hx => ?_⟩
    show extD (Φ a.1) x = Φ b.1 x
    rw [(key a.1 a.2).2 x hx, hab]
  · intro m r p hr α β hα hβ hD x hx
    exact A83Leib.extD_mul hr hα hβ hD hx
  · intro m r p hr α β hα hβ hD
    exact A83Leib.isCr_mul hr hα hβ hD
  · intro m p q α β hα hβ
    exact A83Leib.isDeg_mul hα hβ
  · intro m r a
    exact A83DGA.isCr_const r a
  · intro L _ _ δ
    exact A83DGA.delta_one δ
  · intro m r ω ω' h hC
    exact A83DGA.isCr_of_formEqOn h hC
