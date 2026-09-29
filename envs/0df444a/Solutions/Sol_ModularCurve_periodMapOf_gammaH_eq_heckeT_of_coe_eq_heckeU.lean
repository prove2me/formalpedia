-- Prove2me | solution 1 for ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4ae4b5e2-945c-551f-80a9-4a6508dccc98

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_HeckeEis_coresHom_eq_transfer
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU

set_option autoImplicit false
set_option maxHeartbeats 6400000

open scoped MatrixGroups ModularForm Topology
open UpperHalfPlane CongruenceSubgroup CohCarrier ModularCurve ModularCurve.Period Filter

namespace HeckePeriod

theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ GammaH M H := by
  intro A hA
  rw [mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

scoped instance GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

section

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

theorem heckeT_apply_eq_sum {A : Type*} [AddCommGroup A] (φ : H1 M H A) (γ : ↥(GammaH M H)) :
    letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    heckeT M H q A φ (Additive.ofMul γ) =
      ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q,
        φ (Additive.ofMul (conjL M H q (HeckeEis.transferAux (GammaHUpper M H q) γ c))) := by
  have h := HeckeEis.coresHom_eq_transfer (GammaHUpper M H q) (HeckeEis.pullbackHom (conjL M H q) φ)
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp
    (conjL M H q))) (Additive.ofMul γ) = _
  rw [show (AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H q) =
      AddMonoidHom.toMultiplicativeRight (HeckeEis.pullbackHom (conjL M H q) φ) from rfl, ← h,
    HeckeEis.coresHom_apply]
  rfl

noncomputable def beta (c : ↥(GammaH M H) ⧸ GammaHUpper M H q) : GL (Fin 2) ℝ :=
  ModularForm.heckeMatrix q 0 *
    (Matrix.SpecialLinearGroup.mapGL ℝ (((c.out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)

theorem mapGL_conjL_mul_heckeMatrix (t : ↥(GammaHUpper M H q)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q 0 =
      ModularForm.heckeMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (((t : ↥(GammaH M H)) : SL(2, ℤ))) : GL (Fin 2) ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hdvd : (q : ℤ) ∣ (((t : ↥(GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 :=
    dvd_of_mem_GammaHUpper M H q t
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq]
  have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t : ↥(GammaH M H)) : SL(2, ℤ)) :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((conjUpperMat q ((t : ↥(GammaH M H)) : SL(2, ℤ)) hdvd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := rfl
  have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((t : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((((t : ↥(GammaH M H)) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl
  have hcast : (((((t : ↥(GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / q : ℤ) : ℝ) * q =
      (((((t : ↥(GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hdvd
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hcast, mul_comm]

theorem hasDerivAt_comp_smul (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val) {F : ℍ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ w : ℍ, HasDerivAt (F ∘ ofComplex) (f w) ↑w) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => F (β • ofComplex z)) ((f ∣[(2 : ℤ)] β) τ) ↑τ := by

  set a : ℂ := ((β 0 0 : ℝ) : ℂ)
  set b : ℂ := ((β 0 1 : ℝ) : ℂ)
  set c : ℂ := ((β 1 0 : ℝ) : ℂ)
  set d : ℂ := ((β 1 1 : ℝ) : ℂ)
  set moeb : ℂ → ℂ := fun w => (a * w + b) / (c * w + d) with hmoeb
  have hdet : a * d - b * c = ((β.det.val : ℝ) : ℂ) := by
    simp only [a, b, c, d, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    push_cast; ring
  have hden : ∀ z : ℂ, 0 < z.im → c * z + d ≠ 0 := by
    intro z hz
    have := UpperHalfPlane.denom_ne_zero β (ofComplex z)
    rwa [UpperHalfPlane.denom, ofComplex_apply_of_im_pos hz] at this
  have hmoeb_eq : ∀ z : ℂ, 0 < z.im → ((β • ofComplex z : ℍ) : ℂ) = moeb z := by
    intro z hz
    rw [coe_smul_of_det_pos hβ, UpperHalfPlane.num, UpperHalfPlane.denom, ofComplex_apply_of_im_pos hz]
  have hderiv_moeb : HasDerivAt moeb ((a * d - b * c) / (c * (τ : ℂ) + d) ^ 2) (τ : ℂ) := by
    have hnum : HasDerivAt (fun w : ℂ => a * w + b) a (τ : ℂ) := by
      simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
    have hden' : HasDerivAt (fun w : ℂ => c * w + d) c (τ : ℂ) := by
      simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
    have h := hnum.div hden' (hden _ τ.2)
    convert h using 1 <;> try rfl
    ring
  have hev : (fun z : ℂ => F (β • ofComplex z)) =ᶠ[𝓝 (τ : ℂ)] (fun z : ℂ => (F ∘ ofComplex) (moeb z)) := by
    have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds τ.2] with z hz
    simp only [Function.comp_apply]
    rw [← hmoeb_eq z hz, ofComplex_apply]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : HasDerivAt (F ∘ ofComplex) (f (β • τ)) (moeb (τ : ℂ)) := by
    have := hF (β • τ)
    rwa [show ((β • τ : ℍ) : ℂ) = moeb (τ : ℂ) from by
      rw [← hmoeb_eq (τ : ℂ) τ.2, ofComplex_apply]] at this
  have h := h1.comp (τ : ℂ) hderiv_moeb

  have hval : (f ∣[(2 : ℤ)] β) τ = f (β • τ) * ((a * d - b * c) / (c * (τ : ℂ) + d) ^ 2) := by
    rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hβ, hdet]
    simp only [ContinuousAlgEquiv.refl_apply, abs_of_pos hβ]
    rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, UpperHalfPlane.denom, zpow_neg, zpow_two, div_eq_mul_inv,
      pow_two, mul_assoc]
  rw [hval]
  exact h

theorem periodMapOf_eq_heckeT_of_apply_eq_sum (f g : CuspForm (GammaH M H) 2)
    (hsum : letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
      ∀ τ : ℍ, g τ = ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, (⇑f ∣[(2 : ℤ)] beta M H q c) τ) :
    periodMapOf (GammaH M H) g = heckeT M H q ℂ (periodMapOf (GammaH M H) f) := by
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex

  obtain ⟨F₀, hF₀⟩ := exists_hasEquivariantPrimitiveOf (GammaH M H) f
  obtain ⟨F, hF, hdefF⟩ := periodMapOf_def (GammaH M H) f hF₀
  obtain ⟨G₀, hG₀⟩ := exists_hasEquivariantPrimitiveOf (GammaH M H) g
  obtain ⟨G, hG, hdefG⟩ := periodMapOf_def (GammaH M H) g hG₀
  have hFd := hF.1
  have hFeq := hF.2.2.1

  set Φ : ℍ → ℂ := fun z => ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, F (beta M H q c • z) with hΦ

  have hbeta : ∀ (γ : ↥(GammaH M H)) (d : ↥(GammaH M H) ⧸ GammaHUpper M H q) (z : ℍ),
      beta M H q (γ • d) • ((γ : SL(2, ℤ)) • z) =
        ((conjL M H q (HeckeEis.transferAux (GammaHUpper M H q) γ d) : ↥(GammaH M H)) : SL(2, ℤ)) •
          (beta M H q d • z) := by
    intro γ d z
    set t := HeckeEis.transferAux (GammaHUpper M H q) γ d with ht
    have hrel : (((γ • d).out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ * (γ : SL(2, ℤ)) =
        ((t : ↥(GammaH M H)) : SL(2, ℤ)) * (((d.out : ↥(GammaH M H)) : SL(2, ℤ)))⁻¹ := by
      have : ((t : ↥(GammaH M H)) : SL(2, ℤ)) =
          (((γ • d).out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ * ((γ : SL(2, ℤ)) * ((d.out : ↥(GammaH M H)) : SL(2, ℤ))) := rfl
      rw [this]; group
    show beta M H q (γ • d) • ((Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • z) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
        (beta M H q d • z)
    rw [← mul_smul, ← mul_smul]
    congr 1
    simp only [beta]
    rw [mul_assoc, ← map_mul, hrel, map_mul, ← mul_assoc, ← mapGL_conjL_mul_heckeMatrix, mul_assoc]

  have hcob : ∀ (γ : ↥(GammaH M H)) (z : ℍ),
      Φ ((γ : SL(2, ℤ)) • z) - Φ z = heckeT M H q ℂ hFeq.periodHom (Additive.ofMul γ) := by
    intro γ z
    simp only [hΦ]
    rw [heckeT_apply_eq_sum,
      ← Fintype.sum_bijective (γ • ·) (MulAction.bijective γ)
        (fun d => F (beta M H q (γ • d) • ((γ : SL(2, ℤ)) • z)))
        (fun c => F (beta M H q c • ((γ : SL(2, ℤ)) • z))) (fun d => rfl),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hbeta γ d z, IsEquivariantPrimitive.periodHom_apply, ← hFeq.sub_eq_period _ (beta M H q d • z)]
  have hΦeq : IsEquivariantPrimitive (GammaH M H) Φ := fun γ => ⟨_, hcob γ⟩

  have hbdet : ∀ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, 0 < (beta M H q c).det.val := by
    intro c
    simp only [beta, map_mul, Units.val_mul]
    refine mul_pos (ModularForm.det_heckeMatrix_pos q 0) ?_
    have : ((Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.mapGL ℝ (((c.out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹))).val : ℝ) = 1 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact Matrix.SpecialLinearGroup.det_coe _
    rw [this]; exact one_pos
  have hΦd : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex) (g τ) ↑τ := by
    intro τ
    rw [hsum τ]
    have := HasDerivAt.sum (u := Finset.univ)
      (fun (c : ↥(GammaH M H) ⧸ GammaHUpper M H q) _ => hasDerivAt_comp_smul (beta M H q c) (hbdet c) hFd τ)
    convert this using 1 <;> try rfl
    ext z
    simp only [Function.comp_apply, hΦ, Finset.sum_apply]

  rw [hdefG, hdefF, hG.2.2.1.periodHom_eq_of_hasDerivAt hΦeq hG.1 hΦd]
  refine AddMonoidHom.ext fun x => ?_
  induction x using Additive.rec with
  | ofMul γ =>
  rw [IsEquivariantPrimitive.periodHom_apply, ← hΦeq.sub_eq_period γ UpperHalfPlane.I, hcob γ]

end

end HeckePeriod
p2m_reactivate "P2MW.S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU.HeckePeriod"

namespace HeckePeriod

section Affine

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

def transl (n : ℤ) : ↥(GammaH M H) :=
  ⟨ModularGroup.T ^ n, by
    rw [mem_GammaH_iff]
    have h0 : ModularGroup.T ^ n ∈ Gamma0 M := by
      rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp
    refine ⟨h0, ?_⟩
    have : gamma0Units M ⟨ModularGroup.T ^ n, h0⟩ = 1 := by
      ext; rw [val_gamma0Units]
      show (((ModularGroup.T ^ n) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
      rw [ModularGroup.coe_T_zpow]; simp
    rw [this]; exact one_mem H⟩

@[scoped simp] theorem coe_transl (n : ℤ) : ((transl M H n : ↥(GammaH M H)) : SL(2, ℤ)) = ModularGroup.T ^ n := rfl

theorem exists_add_neg_eq_mul (j : Fin q) : ∃ e : ℕ, (j : ℕ) + ((-j : Fin q) : ℕ) = e * q := by
  have h : ((j : ℕ) + ((-j : Fin q) : ℕ)) % q = 0 := by
    have := Fin.val_add j (-j)
    rw [add_neg_cancel, Fin.val_zero] at this
    exact this.symm
  exact ⟨((j : ℕ) + ((-j : Fin q) : ℕ)) / q, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm⟩

theorem heckeMatrix_zero_mul_mapGL_T_zpow_neg (j : Fin q) (e : ℕ) (he : (j : ℕ) + ((-j : Fin q) : ℕ) = e * q) :
    ModularForm.heckeMatrix q 0 * (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ ((j : ℕ) : ℤ))⁻¹) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
  have hq : q ≠ 0 := NeZero.ne q
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq, ModularForm.val_heckeMatrix hq]
  have e1 : ∀ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ n)⁻¹) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (-n : ℝ); 0, 1] := by
    intro n
    rw [← zpow_neg, show ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (-n))) : GL (Fin 2) ℝ) =
      ((ModularGroup.T ^ (-n) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) from rfl,
      ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [e1, e1]
  have he' : ((j : ℕ) : ℝ) + (((-j : Fin q) : ℕ) : ℝ) = (e : ℝ) * (q : ℝ) := by exact_mod_cast he
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith [he']

theorem bijective_transl (hqM : q ∣ M) :
    Function.Bijective (fun j : Fin q => (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ)) :
      ↥(GammaH M H) ⧸ GammaHUpper M H q)) := by
  have hq : q ≠ 0 := NeZero.ne q
  constructor
  · intro i j hij
    rw [QuotientGroup.eq] at hij
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, coe_transl, ← zpow_neg, ← zpow_add,
      mem_Gamma0Upper, ModularGroup.coe_T_zpow] at hij
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero] at hij

    apply Fin.ext
    have h1 : ((j : ℕ) : ZMod q) = ((i : ℕ) : ZMod q) := by
      have : ((-(i : ℕ) + (j : ℕ) : ℤ) : ZMod q) = 0 := by exact_mod_cast hij
      push_cast at this
      linear_combination this
    have := (ZMod.natCast_eq_natCast_iff' (j : ℕ) (i : ℕ) q).mp h1
    rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at this
    exact this.symm
  · intro c
    induction c using QuotientGroup.induction_on with
    | H γ =>
    obtain ⟨h0, -⟩ := mem_GammaH_iff.mp γ.2

    have hc : ((((γ : SL(2, ℤ)) 1 0 : ℤ)) : ZMod q) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (Int.natCast_dvd_natCast.mpr hqM).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h0))
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
    rw [Matrix.det_fin_two] at hdet
    have had : ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) * ((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod q) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
      exact this

    set jz : ZMod q := ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) with hjz
    refine ⟨⟨jz.val, ZMod.val_lt jz⟩, ?_⟩
    symm
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, mem_Gamma0Upper]

    have hentry : ((γ : SL(2, ℤ))⁻¹ * ModularGroup.T ^ (((jz.val : ℕ) : ℤ)) : SL(2, ℤ)) 0 1 =
        ((γ : SL(2, ℤ)) 1 1 : ℤ) * ((jz.val : ℕ) : ℤ) - ((γ : SL(2, ℤ)) 0 1 : ℤ) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T_zpow,
        Matrix.adjugate_fin_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hentry]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, hjz]
    linear_combination ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * had

theorem sum_slash_beta_eq_heckeU (hqM : q ∣ M) (f : CuspForm (GammaH M H) 2) :
    letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, ⇑f ∣[(2 : ℤ)] beta M H q c) = ModularForm.heckeU 2 q ⇑f := by
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex

  rw [← Fintype.sum_bijective _ (bijective_transl M H q hqM) (fun j => ⇑f ∣[(2 : ℤ)] beta M H q
      (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ)))) _ (fun _ => rfl)]

  have hterm : ∀ j : Fin q, ⇑f ∣[(2 : ℤ)] beta M H q (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
      ⇑f ∣[(2 : ℤ)] ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
    intro j
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GammaHUpper M H q) (transl M H ((j : ℕ) : ℤ))
    obtain ⟨e, he⟩ := exists_add_neg_eq_mul q j
    have hb : beta M H q (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
          ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
      simp only [beta]
      rw [hk, Subgroup.coe_mul, mul_inv_rev, map_mul, ← mul_assoc,
        show (((k : ↥(GammaHUpper M H q)) : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ =
          (((k⁻¹ : ↥(GammaHUpper M H q)) : ↥(GammaH M H)) : SL(2, ℤ)) from rfl,
        ← mapGL_conjL_mul_heckeMatrix, mul_assoc, coe_transl,
        heckeMatrix_zero_mul_mapGL_T_zpow_neg q j e he, ← mul_assoc]
    have hmem1 : (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ (conjL M H q k⁻¹).2
    have hmem2 : (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) ∈
        (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) := by
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← zpow_neg]
      exact (transl M H (-(e : ℤ))).2
    rw [hb, SlashAction.slash_mul, SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f _ hmem1,
      SlashInvariantFormClass.slash_action_eq f _ hmem2]
  simp_rw [hterm]
  rw [ModularForm.heckeU_def, ← Fin.sum_univ_eq_sum_range (fun i => ⇑f ∣[(2 : ℤ)] ModularForm.heckeMatrix q i) q]
  exact Fintype.sum_equiv (Equiv.neg (Fin q)) _ _ (fun j => rfl)

end Affine
p2m_reactivate "P2MW.S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU.HeckePeriod"

end HeckePeriod
p2m_reactivate "P2MW.S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU.HeckePeriod"

open HeckePeriod in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ModularForm.heckeU 2 q ⇑f) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.heckeT M H q ℂ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  apply periodMapOf_eq_heckeT_of_apply_eq_sum
  intro τ
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  rw [hg, ← sum_slash_beta_eq_heckeU M H q hqM f, Finset.sum_apply]

end S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
end P2MW
export P2MW.S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU (solution)
