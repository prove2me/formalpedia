-- Prove2me | solution 1 for ModularCurve.exists_hasEquivariantPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4f86b3d5-1db5-56c7-9ac1-0db5970090ef

import Mathlib
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_hasEquivariantPrimitive

open scoped MatrixGroups Real Manifold ModularForm
open UpperHalfPlane Filter Topology Complex Function Metric

namespace ModularCurve
p2m_export "ModularCurve" "HasEquivariantPrimitive Period.IsEquivariantPrimitive"
namespace PrimitiveConstruction
p2m_open "ModularCurve"

local notation "𝕢" => Function.Periodic.qParam

theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (𝕢 h) (2 * π * Complex.I / h * 𝕢 h z) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * ↑π * Complex.I * w / ↑h)
      (2 * ↑π * Complex.I / ↑h) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * ↑π * Complex.I)).div_const (↑h : ℂ)
  have h2 := h1.cexp
  have hval : 2 * (π:ℂ) * Complex.I / ↑h * 𝕢 h z
      = cexp (2 * ↑π * Complex.I * z / ↑h) * (2 * ↑π * Complex.I / ↑h) := by
    simp only [Function.Periodic.qParam]
    ring
  rw [hval]
  exact h2

theorem exists_primitive {h : ℝ} {g : ℍ → ℂ} (hh : 0 < h) (hper : Periodic (g ∘ ofComplex) h)
    (hhol : MDiff g) (hzero : IsZeroAtImInfty g) :
    ∃ G : ℍ → ℂ, (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) ∧
      Tendsto G atImInfty (𝓝 0) := by
  have hbdd : IsBoundedAtImInfty g := hzero.isBoundedAtImInfty
  set Φ : ℂ → ℂ := cuspFunction h g with hΦ
  have hΦdiff : DifferentiableOn ℂ Φ (ball 0 1) :=
    differentiableOn_cuspFunction_ball hh hper hhol hbdd
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦ, cuspFunction_apply_zero hh (analyticAt_cuspFunction_zero hh hper hhol hbdd) hper]
    exact hzero.valueAtInfty_eq_zero
  set Φ₁ : ℂ → ℂ := dslope Φ 0 with hΦ₁
  have hΦ₁diff : DifferentiableOn ℂ Φ₁ (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hΦdiff
  have hΦ₁mul : ∀ q : ℂ, q * Φ₁ q = Φ q := fun q => by
    have := sub_smul_dslope Φ 0 q
    simpa [hΦ0, smul_eq_mul] using this
  obtain ⟨Ψ, hΨ0, hΨ⟩ := (hΦ₁diff.isExactOn_ball).with_val_at 0 0
  have hqball : ∀ τ : ℍ, 𝕢 h ↑τ ∈ ball (0:ℂ) 1 := by
    intro τ
    rw [mem_ball_zero_iff, Function.Periodic.norm_qParam]
    have him : (0:ℝ) < Complex.im ↑τ := τ.2
    calc Real.exp (-2 * π * Complex.im ↑τ / h) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by
            apply div_neg_of_neg_of_pos _ hh
            nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero
  refine ⟨fun τ : ℍ => ↑h / (2 * π * Complex.I) * Ψ (𝕢 h ↑τ), fun τ => ?_, ?_⟩
  · have hchain : HasDerivAt (fun z : ℂ => ↑h / (2 * π * Complex.I) * Ψ (𝕢 h z)) (g τ) ↑τ := by
      have h1 : HasDerivAt (fun z : ℂ => Ψ (𝕢 h z))
          (Φ₁ (𝕢 h ↑τ) * (2 * π * Complex.I / h * 𝕢 h ↑τ)) ↑τ :=
        (hΨ _ (hqball τ)).comp (↑τ : ℂ) (hasDerivAt_qParam h ↑τ)
      have h2 := h1.const_mul (↑h / (2 * π * Complex.I))
      convert h2 using 1 <;> try rfl
      have hne : (↑h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
      have h3 : ↑h / (2 * ↑π * Complex.I) * (Φ₁ (𝕢 h ↑τ) * (2 * ↑π * Complex.I / ↑h * 𝕢 h ↑τ))
          = 𝕢 h ↑τ * Φ₁ (𝕢 h ↑τ) := by
        field_simp
      rw [h3, hΦ₁mul]
      exact (eq_cuspFunction τ hh.ne' hper).symm
    refine hchain.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  · have hΨcont : ContinuousAt Ψ 0 :=
      (hΨ 0 (mem_ball_self one_pos)).differentiableAt.continuousAt
    have hq0 : Tendsto (fun τ : ℍ => 𝕢 h ↑τ) atImInfty (𝓝 0) :=
      qParam_tendsto_atImInfty hh
    have : Tendsto (fun τ : ℍ => Ψ (𝕢 h ↑τ)) atImInfty (𝓝 (Ψ 0)) :=
      (hΨcont.tendsto).comp hq0
    rw [hΨ0] at this
    simpa using this.const_mul (↑h / (2 * π * Complex.I))

theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

theorem sub_eq_const_of_forall_hasDerivAt {F G : ℂ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt F (f τ) ↑τ) (hG : ∀ τ : ℍ, HasDerivAt G (f τ) ↑τ) :
    ∃ c : ℂ, ∀ τ : ℍ, F ↑τ - G ↑τ = c := by
  refine ⟨F ↑UpperHalfPlane.I - G ↑UpperHalfPlane.I, fun τ => ?_⟩
  exact apply_eq_apply_of_hasDerivAt_zero
    (D := fun z => F z - G z) (fun σ => by have h := (hF σ).sub (hG σ); rw [sub_self] at h; exact h) τ UpperHalfPlane.I

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z)) ((g ∣[(2:ℤ)] γ) τ) ↑τ := by
  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rw [← hfun] at hcomp
  convert hcomp using 1 <;> try rfl
  exact ModularForm.SL_slash_apply (g : ℍ → ℂ) γ τ

section Assembly

open CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped Pointwise in
theorem natCast_mem_strictPeriods_conj {Γ : Subgroup SL(2, ℤ)} {N : ℕ}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (δ : SL(2, ℤ)) :
    (N : ℝ) ∈ Subgroup.strictPeriods
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹ •
        (Γ : Subgroup (GL (Fin 2) ℝ))) := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul]
  have hT1 : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T
      = Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
    rw [Units.ext_iff, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.GeneralLinearGroup.upperRightHom_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hTN : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ))
      = Matrix.GeneralLinearGroup.upperRightHom (N : ℝ) := by
    rw [zpow_natCast, map_pow, hT1, ← AddChar.map_nsmul_eq_pow]
    norm_num
  rw [← hTN, ← map_mul, ← map_inv, ← map_mul]
  refine Subgroup.mem_map_of_mem _ (hΓ ?_)
  have hTmem : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  exact (CongruenceSubgroup.Gamma_normal N).conj_mem _ hTmem δ

variable {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] (f : F)

theorem periodic_slash_comp_ofComplex {N : ℕ}
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (δ : SL(2, ℤ)) :
    Periodic (((f : ℍ → ℂ) ∣[k] δ) ∘ ofComplex) (N : ℝ) :=
  SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ δ))
    (natCast_mem_strictPeriods_conj hΓ δ)

theorem SL_slash_eq_self_of_mem [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) : (f : ℍ → ℂ) ∣[k] γ = f :=
  SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

variable {N : ℕ} [NeZero N] [CuspFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) 2]

theorem exists_equivariantPrimitive (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    ∃ Fprim : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) ∧
      Tendsto Fprim atImInfty (𝓝 0) ∧
      ModularCurve.Period.IsEquivariantPrimitive Γ Fprim ∧
      ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => Fprim (δ • w)) atImInfty (𝓝 L) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hN : (0:ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hmaster : ∀ δ : SL(2, ℤ), ∃ G : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (((f : ℍ → ℂ) ∣[(2:ℤ)] δ) τ) ↑τ) ∧
      Tendsto G atImInfty (𝓝 0) := fun δ =>
    exists_primitive hN (periodic_slash_comp_ofComplex f hΓ δ)
      ((CuspFormClass.holo f).slash 2 _) (CuspFormClass.zero_at_infty_slash f δ)
  obtain ⟨Fprim, hFprim, hFprim0⟩ := hmaster 1
  have hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ := by
    intro τ
    simpa using hFprim τ
  refine ⟨Fprim, hFf, hFprim0, ?_, ?_⟩
  · intro γ
    have hslash : ((f : ℍ → ℂ) ∣[(2:ℤ)] (γ : SL(2, ℤ))) = f := SL_slash_eq_self_of_mem f γ.2
    have hchain : ∀ τ : ℍ, HasDerivAt (fun z : ℂ => Fprim ((γ : SL(2, ℤ)) • ofComplex z))
        (f τ) ↑τ := by
      intro τ
      have := hasDerivAt_comp_smul hFf (γ : SL(2, ℤ)) τ
      rwa [hslash] at this
    obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hchain hFf
    exact ⟨c, fun z => by simpa using hc z⟩
  · intro δ
    obtain ⟨Gδ, hGδ, hGδ0⟩ := hmaster δ
    have hchain : ∀ τ : ℍ, HasDerivAt (fun z : ℂ => Fprim (δ • ofComplex z))
        (((f : ℍ → ℂ) ∣[(2:ℤ)] δ) τ) ↑τ := fun τ => hasDerivAt_comp_smul hFf δ τ
    obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hchain hGδ
    refine ⟨c, ?_⟩
    have h1 : (fun w : ℍ => Fprim (δ • w)) = fun w : ℍ => (Gδ ∘ ofComplex) ↑w + c := by
      funext w
      have := hc w
      simp only [ofComplex_apply] at this ⊢
      linear_combination this
    rw [h1]
    have : Tendsto (fun w : ℍ => (Gδ ∘ ofComplex) ↑w) atImInfty (𝓝 0) := by
      simpa [Function.comp_def, ofComplex_apply] using hGδ0
    simpa using this.add_const c

end Assembly

theorem Gamma_le_Gamma0 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma0 N :=
  fun _ hA => CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hA).2.2.1

theorem main (N : ℕ) [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∃ F : ℍ → ℂ, ModularCurve.HasEquivariantPrimitive N f F :=
  exists_equivariantPrimitive f (Gamma_le_Gamma0 N)

end ModularCurve.PrimitiveConstruction

theorem solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∃ F : UpperHalfPlane → ℂ, ModularCurve.HasEquivariantPrimitive N f F :=
  ModularCurve.PrimitiveConstruction.main N f

end S_ModularCurve_exists_hasEquivariantPrimitive
end P2MW
export P2MW.S_ModularCurve_exists_hasEquivariantPrimitive (solution)
