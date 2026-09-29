-- Prove2me | solution 1 for ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/de67bbe1-f00e-5dae-82fc-51158c9e1af3

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH
import Theorems.Thm_ModularForm_heckeU_add_slash_slash_eq_self_of_mem_GammaH
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Manifold Topology
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "periodAlongOf periodAlongOf_apply periodOf periodLatticeOf periodOf_mem_periodLatticeOf clamp01 clamp01_of_mem segmentPoint continuous_segmentPoint segmentPath continuous_segmentPath periodAlong period"
p2m_open "ModularCurve"

namespace PeriodLatticeHStableProof

def IsPrimitive (h : ℍ → ℂ) (G : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, HasDerivAt G (h τ) (τ : ℂ)

theorem IsPrimitive.add {h₁ h₂ : ℍ → ℂ} {G₁ G₂ : ℂ → ℂ} (h1 : IsPrimitive h₁ G₁)
    (h2 : IsPrimitive h₂ G₂) : IsPrimitive (h₁ + h₂) (G₁ + G₂) :=
  fun τ => (h1 τ).add (h2 τ)

theorem IsPrimitive.sum {ι : Type*} (s : Finset ι) {h : ι → ℍ → ℂ} {G : ι → ℂ → ℂ}
    (hG : ∀ i ∈ s, IsPrimitive (h i) (G i)) :
    IsPrimitive (∑ i ∈ s, h i) (fun z => ∑ i ∈ s, G i z) := by
  intro τ
  have h' : (fun z => ∑ i ∈ s, G i z) = ∑ i ∈ s, G i := by
    ext z; simp [Finset.sum_apply]
  have := HasDerivAt.sum (u := s) (A := G) (A' := fun i => h i τ) (x := (τ : ℂ))
    (fun i hi => hG i hi τ)
  rw [h']
  simpa [Finset.sum_apply] using this

theorem IsPrimitive.exists_const {h : ℍ → ℂ} {G G' : ℂ → ℂ} (hG : IsPrimitive h G)
    (hG' : IsPrimitive h G') : ∃ a : ℂ, ∀ τ : ℍ, G τ = G' τ + a := by
  obtain ⟨a, ha⟩ := isOpen_upperHalfPlaneSet.exists_eq_add_of_deriv_eq
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun z hz => (hG ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG' ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hG ⟨z, hz⟩).deriv, (hG' ⟨z, hz⟩).deriv])
  exact ⟨a, fun τ => ha τ.im_pos⟩

theorem exists_isPrimitive {h : ℍ → ℂ} (hh : MDiff h) : ∃ G : ℂ → ℂ, IsPrimitive h G := by
  have hF : DifferentiableOn ℂ (h ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hh

  let r : ℕ → ℝ := fun n => (n : ℝ) + 1
  let c : ℕ → ℂ := fun n => (r n : ℂ) * Complex.I
  have hr : ∀ n, 0 < r n := fun n => by positivity
  have hc_im : ∀ n, (c n).im = r n := fun n => by simp [c]
  have hc_re : ∀ n, (c n).re = 0 := fun n => by simp [c]
  have hsub : ∀ n, Metric.ball (c n) (r n) ⊆ {z : ℂ | 0 < z.im} := by
    intro n z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : |(z - c n).im| ≤ ‖z - c n‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hc_im] at h1
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hz)).1
    show 0 < z.im
    linarith
  have hI : ∀ n, Complex.I ∈ Metric.ball (c n) (r n) := by
    intro n
    rw [Metric.mem_ball, Complex.dist_eq]
    have : Complex.I - c n = ((1 - r n : ℝ) : ℂ) * Complex.I := by
      simp only [c]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    simp only [r]
    rw [abs_lt]; constructor <;> linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcover : ∀ z : ℂ, 0 < z.im → ∃ n : ℕ, z ∈ Metric.ball (c n) (r n) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (‖z‖ ^ 2 / (2 * z.im))
    refine ⟨n, ?_⟩
    rw [Metric.mem_ball, Complex.dist_eq]
    have hn' : ‖z‖ ^ 2 / (2 * z.im) < r n := lt_of_lt_of_le hn (by simp [r])
    have h2 : ‖z‖ ^ 2 < 2 * z.im * r n := by
      rwa [div_lt_iff₀ (by positivity), mul_comm] at hn'
    have hsq : ‖z - c n‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.im * r n + r n ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
        Complex.sub_re, Complex.sub_im, hc_re, hc_im]
      ring
    have h3 : ‖z - c n‖ ^ 2 < r n ^ 2 := by rw [hsq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (hr n).le h3
  have hmono : ∀ {n m : ℕ}, n ≤ m → Metric.ball (c n) (r n) ⊆ Metric.ball (c m) (r m) := by
    intro n m hnm z hz
    rw [Metric.mem_ball] at hz ⊢
    have hd : dist (c n) (c m) = r m - r n := by
      rw [Complex.dist_eq]
      have : c n - c m = ((r n - r m : ℝ) : ℂ) * Complex.I := by
        simp only [c]; push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_sub_comm, abs_of_nonneg]
      simp only [r]; linarith [(Nat.cast_le.mpr hnm : (n : ℝ) ≤ m)]
    calc dist z (c m) ≤ dist z (c n) + dist (c n) (c m) := dist_triangle _ _ _
      _ < r n + (r m - r n) := by rw [hd]; linarith
      _ = r m := by ring

  have hex : ∀ n, ∃ g : ℂ → ℂ, g Complex.I = 0 ∧
      ∀ z ∈ Metric.ball (c n) (r n), HasDerivAt g ((h ∘ ofComplex) z) z :=
    fun n => ((hF.mono (hsub n)).isExactOn_ball).with_val_at Complex.I 0
  choose g hg0 hg using hex
  have hagree : ∀ {n m : ℕ}, n ≤ m → Set.EqOn (g n) (g m) (Metric.ball (c n) (r n)) := by
    intro n m hnm
    refine Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected ?_ ?_ ?_ (hI n) ?_
    · exact fun z hz => (hg n z hz).differentiableAt.differentiableWithinAt
    · exact fun z hz => (hg m z (hmono hnm hz)).differentiableAt.differentiableWithinAt
    · exact fun z hz => by rw [(hg n z hz).deriv, (hg m z (hmono hnm hz)).deriv]
    · rw [hg0, hg0]
  classical
  let idx : ℂ → ℕ := fun z => if hz : 0 < z.im then Nat.find (hcover z hz) else 0
  have hidx : ∀ z : ℂ, (hz : 0 < z.im) → z ∈ Metric.ball (c (idx z)) (r (idx z)) := by
    intro z hz
    simp only [idx, dif_pos hz]
    exact Nat.find_spec (hcover z hz)
  refine ⟨fun z => g (idx z) z, fun τ => ?_⟩
  have hτ := hidx τ τ.im_pos
  have key : (fun z => g (idx z) z) =ᶠ[𝓝 (τ : ℂ)] g (idx τ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hτ] with w hw
    have hw' : 0 < w.im := hsub _ hw
    rcases le_total (idx w) (idx (τ : ℂ)) with hle | hle
    · exact hagree hle (hidx w hw')
    · exact (hagree hle hw).symm
  have := (hg (idx (τ : ℂ)) τ hτ).congr_of_eventuallyEq key
  simpa [Function.comp, ofComplex_apply] using this

theorem IsPrimitive.integral_segment_eq {h : ℍ → ℂ} {G : ℂ → ℂ} (hG : IsPrimitive h G)
    (hc : Continuous h) (τ₀ τ₁ : ℍ) :
    ∫ t in (0 : ℝ)..1, h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) = G τ₁ - G τ₀ := by
  have h0 : segmentPoint τ₀ τ₁ 0 = τ₀ := by simp [segmentPoint, clamp01]
  have h1 : segmentPoint τ₀ τ₁ 1 = τ₁ := by simp [segmentPoint, clamp01]
  have hcontG : Continuous fun t => G (segmentPoint τ₀ τ₁ t) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (g := G) (f := segmentPoint τ₀ τ₁) (x := t)
        (hG (segmentPath τ₀ τ₁ t)).continuousAt (continuous_segmentPoint τ₀ τ₁).continuousAt
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun t => G (segmentPoint τ₀ τ₁ t)) (h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hs : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * (τ₀ : ℂ) + (s : ℂ) * τ₁)
        ((τ₁ : ℂ) - τ₀) t := by
      have := ((hs.const_sub 1).mul_const (τ₀ : ℂ)).add (hs.mul_const (τ₁ : ℂ))
      convert this using 1 <;> try rfl
      ring
    have heq : segmentPoint τ₀ τ₁ =ᶠ[𝓝 t] fun s : ℝ => (1 - (s : ℂ)) * (τ₀ : ℂ) + (s : ℂ) * τ₁ := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [segmentPoint, clamp01_of_mem (Set.Ioo_subset_Icc_self hs), Complex.real_smul,
        Complex.real_smul]
      push_cast
      ring
    have hseg : HasDerivAt (segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t :=
      hlin.congr_of_eventuallyEq heq
    exact (hG (segmentPath τ₀ τ₁ t)).comp t hseg
  have hint : IntervalIntegrable (fun t => h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀))
      MeasureTheory.volume 0 1 :=
    ((hc.comp (continuous_segmentPath τ₀ τ₁)).mul continuous_const).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcontG.continuousOn hderiv
    hint, h0, h1]

theorem IsPrimitive.slash_two {f : ℍ → ℂ} {G : ℂ → ℂ} (hG : IsPrimitive f G)
    {α : GL (Fin 2) ℝ} (hα : 0 < (α.det : ℝ)) :
    IsPrimitive (f ∣[(2 : ℤ)] α) (fun z => G (↑(α • ofComplex z))) := by
  have hα' : 0 < α.val.det := by rwa [Matrix.GeneralLinearGroup.val_det_apply] at hα
  intro τ
  have h1 : HasDerivAt (fun z : ℂ => ((α • ofComplex z : ℍ) : ℂ)) (↑(α.val.det) / denom α τ ^ 2) τ :=
    (hasStrictDerivAt_smul hα' τ).hasDerivAt
  have h2 : HasDerivAt G (f (α • τ)) ((fun z : ℂ => ((α • ofComplex z : ℍ) : ℂ)) τ) := by
    simp only [ofComplex_apply]
    exact hG (α • τ)
  have h3 := h2.comp (τ : ℂ) h1
  convert h3 using 1 <;> try rfl
  have hσ : σ α = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hα']
  rw [ModularForm.slash_apply, hσ, abs_of_pos hα, ← Matrix.GeneralLinearGroup.val_det_apply]
  simp only [ContinuousAlgEquiv.refl_apply]
  rw [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, zpow_neg, zpow_ofNat]
  have hd : denom α τ ≠ 0 := denom_ne_zero α τ
  field_simp

theorem slash_zero_apply_of_det_eq_one (g : ℍ → ℂ) {γ : GL (Fin 2) ℝ} (hγ : γ.det = 1) (τ : ℍ) :
    (g ∣[(0 : ℤ)] γ) τ = g (γ • τ) := by
  have hσ : σ γ = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hγ]
  rw [ModularForm.slash_apply, hσ, hγ]
  simp

theorem slash_zero_apply_of_det_pos (g : ℍ → ℂ) {α : GL (Fin 2) ℝ} (hα : 0 < (α.det : ℝ))
    (τ : ℍ) : (g ∣[(0 : ℤ)] α) τ = ((α.det : ℝ) : ℂ)⁻¹ * g (α • τ) := by
  have hα' : 0 < α.val.det := by rwa [Matrix.GeneralLinearGroup.val_det_apply] at hα
  have hσ : σ α = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hα']
  rw [ModularForm.slash_apply, hσ, abs_of_pos hα]
  simp [mul_comm]

abbrev GammaHGL (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def Φ (τ : ℍ) : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
  periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ

variable {M H}

theorem Φ_apply_of_isPrimitive (τ : ℍ) (f : CuspForm (CohCarrier.GammaH M H) 2)
    {G : ℂ → ℂ} (hG : IsPrimitive ⇑f G) : Φ M H τ f = G τ - G UpperHalfPlane.I := by
  show periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ f = _
  rw [periodAlongOf_apply]
  exact hG.integral_segment_eq (CuspFormClass.holo f).continuous _ _

theorem period_eq_Φ (g : CohCarrier.GammaH M H) :
    periodOf (CohCarrier.GammaH M H) g = Φ M H ((g : SL(2, ℤ)) • UpperHalfPlane.I) := rfl

theorem Φ_smul_sub_Φ (g : CohCarrier.GammaH M H) (τ : ℍ) :
    Φ M H ((g : SL(2, ℤ)) • τ) - Φ M H τ = periodOf (CohCarrier.GammaH M H) g := by
  apply LinearMap.ext
  intro f
  obtain ⟨G, hG⟩ := exists_isPrimitive (CuspFormClass.holo f)
  have hmem : ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ GammaHGL M H :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) g.2
  have hinv : (⇑f) ∣[(2 : ℤ)] ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑f :=
    SlashInvariantForm.slash_action_eqn f _ hmem
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) : ℝ)) := by
    simp
  have hG' : IsPrimitive ⇑f (fun z => G ↑(((g : SL(2, ℤ)) : GL (Fin 2) ℝ) • ofComplex z)) := by
    have := hG.slash_two hdet
    rwa [hinv] at this
  obtain ⟨a, ha⟩ := hG'.exists_const hG
  have ha' : ∀ τ : ℍ, G ↑((g : SL(2, ℤ)) • τ) = G τ + a := fun τ => by
    simpa [ofComplex_apply] using ha τ
  rw [LinearMap.sub_apply, period_eq_Φ, Φ_apply_of_isPrimitive _ f hG,
    Φ_apply_of_isPrimitive _ f hG, Φ_apply_of_isPrimitive _ f hG, ha', ha']
  ring

theorem Φ_smul_sub_Φ_mem {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    Φ M H (γ • τ) - Φ M H τ ∈ periodLatticeOf (CohCarrier.GammaH M H) := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  have := Φ_smul_sub_Φ (M := M) (H := H) ⟨g, hg⟩ τ
  rw [ModularGroup.sl_moeb] at this
  rw [show Matrix.SpecialLinearGroup.mapGL ℝ g • τ = ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) • τ from rfl,
    this]
  exact periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) _

theorem mkQ_Φ_smul {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (γ • τ)) = (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H τ) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Φ_smul_sub_Φ_mem hγ τ

section Engine

variable {ι : Type*} [Fintype ι] (A : ι → GL (Fin 2) ℝ)

theorem dualMap_period_eq (hA : ∀ i, 0 < ((A i).det : ℝ))
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i)
    (g : CohCarrier.GammaH M H) :
    T.dualMap (periodOf (CohCarrier.GammaH M H) g) =
      ∑ i, (Φ M H (A i • (g : SL(2, ℤ)) • UpperHalfPlane.I) - Φ M H (A i • UpperHalfPlane.I)) := by
  apply LinearMap.ext
  intro f
  obtain ⟨G, hG⟩ := exists_isPrimitive (CuspFormClass.holo f)

  have hprim : IsPrimitive ⇑(T f) (fun z => ∑ i, G ↑(A i • ofComplex z)) := by
    rw [hT]
    exact IsPrimitive.sum Finset.univ (fun i _ => hG.slash_two (hA i))
  rw [LinearMap.dualMap_apply, period_eq_Φ, Φ_apply_of_isPrimitive _ _ hprim,
    LinearMap.sum_apply]
  simp only [LinearMap.sub_apply, Φ_apply_of_isPrimitive _ f hG, ofComplex_apply,
    Finset.sum_sub_distrib]
  ring

theorem sum_mkQ_Φ_smul_eq {d : ℝ} (hd : 0 < d) (hA : ∀ i, ((A i).det : ℝ) = d)
    (hstab : ∀ g : ℍ → ℂ, (∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g) →
      ∀ γ ∈ GammaHGL M H, (∑ i, g ∣[(0 : ℤ)] A i) ∣[(0 : ℤ)] γ = ∑ i, g ∣[(0 : ℤ)] A i)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    ∑ i, (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (A i • γ • τ)) = ∑ i, (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (A i • τ)) := by
  classical
  set Φb : ℍ → (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)) ⧸ periodLatticeOf (CohCarrier.GammaH M H) :=
    fun τ => (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H τ) with hΦb
  have hΦb_inv : ∀ γ ∈ GammaHGL M H, ∀ τ : ℍ, Φb (γ • τ) = Φb τ := fun γ hγ τ => mkQ_Φ_smul hγ τ
  have hAdet : ∀ i, 0 < ((A i).det : ℝ) := fun i => (hA i).symm ▸ hd

  have hcount : ∀ v, (Finset.univ.filter fun i => v = Φb (A i • γ • τ)).card =
      (Finset.univ.filter fun i => v = Φb (A i • τ)).card := by
    intro v
    let g : ℍ → ℂ := fun τ => if v = Φb τ then 1 else 0
    have hg : ∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g := by
      intro γ hγ
      funext τ
      rw [slash_zero_apply_of_det_eq_one g (Subgroup.HasDetOne.det_eq hγ)]
      simp only [g, hΦb_inv γ hγ]
    have key := congr_fun (hstab g hg γ hγ) τ
    rw [slash_zero_apply_of_det_eq_one _ (Subgroup.HasDetOne.det_eq hγ)] at key
    simp only [Finset.sum_apply, slash_zero_apply_of_det_pos _ (hAdet _), hA,
      ← Finset.mul_sum] at key
    have hd' : ((d : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd.ne')
    have key' := mul_left_cancel₀ hd' key
    simp only [g, Finset.sum_boole] at key'
    exact_mod_cast key'
  have hms : (Finset.univ.val.map fun i => Φb (A i • γ • τ)) =
      Finset.univ.val.map fun i => Φb (A i • τ) := by
    refine Multiset.ext.mpr fun v => ?_
    rw [Multiset.count_map, Multiset.count_map]
    have := hcount v
    simpa [Finset.card_def, Finset.filter_val] using this
  show ∑ i, Φb (A i • γ • τ) = ∑ i, Φb (A i • τ)
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, hms]

theorem dualMap_period_mem {d : ℝ} (hd : 0 < d) (hA : ∀ i, ((A i).det : ℝ) = d)
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i)
    (hstab : ∀ g : ℍ → ℂ, (∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g) →
      ∀ γ ∈ GammaHGL M H, (∑ i, g ∣[(0 : ℤ)] A i) ∣[(0 : ℤ)] γ = ∑ i, g ∣[(0 : ℤ)] A i)
    (g : CohCarrier.GammaH M H) :
    T.dualMap (periodOf (CohCarrier.GammaH M H) g) ∈ periodLatticeOf (CohCarrier.GammaH M H) := by
  have hAdet : ∀ i, 0 < ((A i).det : ℝ) := fun i => (hA i).symm ▸ hd
  rw [dualMap_period_eq A hAdet T hT g, ← Submodule.ker_mkQ (periodLatticeOf (CohCarrier.GammaH M H)), LinearMap.mem_ker,
    map_sum]
  simp only [map_sub, Finset.sum_sub_distrib]
  have hmem : ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ GammaHGL M H :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) g.2
  have := sum_mkQ_Φ_smul_eq A hd hA hstab hmem UpperHalfPlane.I
  simp only [ModularGroup.sl_moeb]
  rw [this, sub_self]

end Engine

section Instances

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem heckeU_eq_sum (k : ℤ) (p : ℕ) (f : ℍ → ℂ) :
    ModularForm.heckeU k p f = ∑ j : Fin p, f ∣[k] ModularForm.heckeMatrix p j := by
  rw [ModularForm.heckeU_def, Finset.sum_range]

def heckeTFamilyH (M : ℕ) [NeZero M] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    Option (Fin ℓ) → GL (Fin 2) ℝ :=
  fun o => o.elim
    ((Matrix.SpecialLinearGroup.mapGL ℝ
        ((CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) : CongruenceSubgroup.Gamma0 M) :
          SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ)
    fun j => ModularForm.heckeMatrix ℓ j

theorem sum_slash_heckeTFamilyH (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : ℍ → ℂ) :
    ∑ o, f ∣[k] heckeTFamilyH M hℓ hℓM o =
      ModularForm.heckeU k ℓ f +
        f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          ((CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) : CongruenceSubgroup.Gamma0 M) :
            SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) := by
  rw [Fintype.sum_option, heckeU_eq_sum, add_comm]
  rfl

theorem det_heckeTFamilyH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (o : Option (Fin ℓ)) :
    ((heckeTFamilyH M hℓ hℓM o).det : ℝ) = ℓ := by
  cases o with
  | none =>
    show (((Matrix.SpecialLinearGroup.mapGL ℝ _ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ).det : ℝ) = ℓ
    rw [map_mul, Units.val_mul, ModularForm.det_heckeDiagMatrix hℓ.ne_zero]
    simp
  | some j => exact ModularForm.det_heckeMatrix hℓ.ne_zero j

theorem heckeTLinH_dualMap_period_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (g : CohCarrier.GammaH M H) :
    (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine dualMap_period_mem (heckeTFamilyH M hℓ hℓM) (d := (ℓ : ℝ)) (by exact_mod_cast hℓ.pos)
    (det_heckeTFamilyH hℓ hℓM) _ (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM), sum_slash_heckeTFamilyH]
  · rw [sum_slash_heckeTFamilyH]
    exact ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH M H 0 hℓ hℓM _
      (CuspForm.gammaLift_apply_11 hℓ hℓM) hg γ hγ

theorem heckeULinH_dualMap_period_mem {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (g : CohCarrier.GammaH M H) :
    (CuspForm.heckeULinH 2 q).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  refine dualMap_period_mem (fun j : Fin q => ModularForm.heckeMatrix q j) (d := (q : ℝ))
    (by exact_mod_cast hq.pos) (fun j => ModularForm.det_heckeMatrix hq.ne_zero j) _
    (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM), heckeU_eq_sum]
  · rw [← heckeU_eq_sum]
    exact ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H 0 hq hqM hg γ hγ

theorem diamondLinH_dualMap_period_mem (d : (ZMod M)ˣ) (g : CohCarrier.GammaH M H) :
    (CuspForm.diamondLinH 2 d).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  set σ : CongruenceSubgroup.Gamma0 M := CuspForm.gammaLift M d with hσ
  refine dualMap_period_mem (fun _ : Unit => (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))
    (d := (1 : ℝ)) one_pos (fun _ => by simp) _ (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [Fintype.sum_unique, CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2)]
  · rw [Fintype.sum_unique]
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
    have hconj : (σ : SL(2, ℤ)) * γ₀ * (σ : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH M H :=
      CohCarrier.conj_mem_GammaH M H σ ⟨γ₀, hγ₀⟩
    have e : (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((σ : SL(2, ℤ)) * γ₀ * (σ : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
      rw [← map_mul, ← map_mul, inv_mul_cancel_right]
    show (g ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[(0 : ℤ)]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) =
      g ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, e, SlashAction.slash_mul, hg _ (Subgroup.mem_map_of_mem _ hconj)]

end Instances

end PeriodLatticeHStableProof

section Final

open PeriodLatticeHStableProof

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

omit [NeZero M] in
private theorem span_stable (T : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) →ₗ[ℂ]
      Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2))
    (hT : ∀ g : CohCarrier.GammaH M H, T (periodOf (CohCarrier.GammaH M H) g) ∈ periodLatticeOf (CohCarrier.GammaH M H)) :
    ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H), T v ∈ periodLatticeOf (CohCarrier.GammaH M H) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨g, rfl⟩ := h
    exact hT g
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ a hx

theorem periodLatticeOf_stable_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H) :=
  span_stable M H _ (heckeTLinH_dualMap_period_mem hℓ hℓM)

theorem periodLatticeOf_stable_heckeULinH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) :
    ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H) :=
  span_stable M H _ (heckeULinH_dualMap_period_mem hq hqM)

theorem periodLatticeOf_stable_diamondLinH (d : (ZMod M)ˣ) :
    ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H) :=
  span_stable M H _ (diamondLinH_dualMap_period_mem d)

end Final

end ModularCurve

end

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :=
  ⟨fun _ hℓ hℓM => ModularCurve.periodLatticeOf_stable_heckeTLinH M H hℓ hℓM,
    fun _ hq hqM => ModularCurve.periodLatticeOf_stable_heckeULinH M H hq hqM,
    fun d => ModularCurve.periodLatticeOf_stable_diamondLinH M H d⟩

end S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable
end P2MW
export P2MW.S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable (solution)
