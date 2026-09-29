-- Prove2me | solution 1 for ModularCurve.periodMap_rescaleLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/890da73f-f315-5d1f-bcfb-e8fac6592d45

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_ModularCurve_periodMap_eq_periodHom
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMap_rescaleLin_apply

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped MatrixGroups ModularForm
open UpperHalfPlane CongruenceSubgroup ModularCurve ModularCurve.Period

namespace PeriodRescale

theorem diagMatInt_mul_eq {R M d : ℕ} [NeZero d] (h : CohCarrier.LevelLE R M ⊤ ⊤ d)
    (γ : ↥(CohCarrier.GammaH M ⊤)) :
    FreyPackage.ModMCarrier.diagMatInt d * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((CohCarrier.iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        FreyPackage.ModMCarrier.diagMatInt d := by
  have hdvd : (d : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := h.dvd_entry γ
  unfold FreyPackage.ModMCarrier.diagMatInt
  have hmat : ((CohCarrier.iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * d;
         ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / d, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1] := rfl
  rw [hmat, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Int.ediv_mul_cancel hdvd]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem heckeDiagMatrix_mul_mapGL {R M d : ℕ} [NeZero d] (h : CohCarrier.LevelLE R M ⊤ ⊤ d)
    (γ : ↥(CohCarrier.GammaH M ⊤)) :
    ModularForm.heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)) *
        ModularForm.heckeDiagMatrix d := by
  have hd : d ≠ 0 := NeZero.ne d
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) := rfl
  have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)) :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (((CohCarrier.iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) := rfl
  rw [e1, e2, ← FreyPackage.ModMCarrier.diagMatInt_map_eq hd, ← Matrix.map_mul, ← Matrix.map_mul,
    diagMatInt_mul_eq h γ]

end PeriodRescale

open PeriodRescale in
theorem solution
    {R M d : ℕ} [NeZero R] [NeZero M] [NeZero d] (hdRM : d * R ∣ M)
    (h : CohCarrier.LevelLE R M ⊤ ⊤ d)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (γ : ↥(CohCarrier.GammaH M ⊤)) :
    ModularCurve.periodMap M (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)
        (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) =
      ModularCurve.periodMap R f
        (Additive.ofMul ⟨(CohCarrier.iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)),
          CohCarrier.GammaH_le_Gamma0 ⊤ (CohCarrier.iotaDeg R M ⊤ ⊤ d h γ).2⟩) := by
  have hd : d ≠ 0 := NeZero.ne d
  obtain ⟨F, hFd, -, hFeq, -⟩ := CuspForm.exists_equivariantPrimitive_gamma0 f

  have hact : ∀ (s : SL(2, ℤ)) (z : ℍ), s • z = (Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) • z :=
    fun s z => rfl

  have hconj : ∀ (γ' : ↥(CohCarrier.GammaH M ⊤)) (z : ℍ),
      ModularForm.heckeDiagMatrix d • ((γ' : SL(2, ℤ)) • z) = (CohCarrier.iotaDeg R M ⊤ ⊤ d h γ' : SL(2, ℤ)) • (ModularForm.heckeDiagMatrix d • z) := by
    intro γ' z
    rw [hact, hact, ← mul_smul, ← mul_smul, heckeDiagMatrix_mul_mapGL h γ']

  set G : ℍ → ℂ := fun τ => F (ModularForm.heckeDiagMatrix d • τ) with hG
  have hmemH : ∀ g : Gamma0 M, (g : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊤ := fun g => by
    rw [CohCarrier.GammaH_top]; exact g.2
  have hGeq : IsEquivariantPrimitive (Gamma0 M) G := by
    intro g
    set g' : ↥(CohCarrier.GammaH M ⊤) := ⟨(g : SL(2, ℤ)), hmemH g⟩ with hg'
    obtain ⟨c, hc⟩ := hFeq ⟨(CohCarrier.iotaDeg R M ⊤ ⊤ d h g' : SL(2, ℤ)),
      CohCarrier.GammaH_le_Gamma0 ⊤ (CohCarrier.iotaDeg R M ⊤ ⊤ d h g').2⟩
    refine ⟨c, fun z => ?_⟩
    simp only [hG]
    have : (g : SL(2, ℤ)) = (g' : SL(2, ℤ)) := rfl
    rw [this, hconj g' z]
    exact hc (ModularForm.heckeDiagMatrix d • z)
  have hGd : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) ((FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) τ) ↑τ := by
    intro τ
    have hval : (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) τ = (d : ℂ) * f (ModularForm.heckeDiagMatrix d • τ) := by
      rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, ModularForm.slash_heckeDiagMatrix_apply 2 hd,
        show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one]
    rw [hval]

    have hev : (G ∘ ofComplex) =ᶠ[nhds (τ : ℂ)] (fun z : ℂ => (F ∘ ofComplex) ((d : ℂ) * z)) := by
      have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds τ.2] with z hz
      simp only [Function.comp_apply, hG]
      congr 1
      apply UpperHalfPlane.ext
      rw [ModularForm.coe_heckeDiagMatrix_smul hd, ofComplex_apply_of_im_pos hz]
      have hz' : 0 < ((d : ℂ) * z).im := by
        rw [Complex.mul_im]; simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
        exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hd) hz
      rw [ofComplex_apply_of_im_pos hz']
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    have h1 : HasDerivAt (F ∘ ofComplex) (f (ModularForm.heckeDiagMatrix d • τ)) ((d : ℂ) * (τ : ℂ)) := by
      have := hFd (ModularForm.heckeDiagMatrix d • τ)
      rwa [ModularForm.coe_heckeDiagMatrix_smul hd] at this
    have h2 : HasDerivAt (fun z : ℂ => (d : ℂ) * z) (d : ℂ) (τ : ℂ) := by
      simpa using (hasDerivAt_id (τ : ℂ)).const_mul (d : ℂ)
    have := h1.comp (τ : ℂ) h2
    rwa [mul_comm] at this

  rw [periodMap_eq_periodHom hGeq hGd, periodMap_eq_periodHom hFeq hFd,
    IsEquivariantPrimitive.periodHom_apply, IsEquivariantPrimitive.periodHom_apply,
    ← hGeq.sub_eq_period _ UpperHalfPlane.I, ← hFeq.sub_eq_period _ (ModularForm.heckeDiagMatrix d • UpperHalfPlane.I)]
  simp only [hG]
  show F (ModularForm.heckeDiagMatrix d • ((γ : SL(2, ℤ)) • UpperHalfPlane.I)) - F (ModularForm.heckeDiagMatrix d • UpperHalfPlane.I) = _
  rw [hconj γ]

end S_ModularCurve_periodMap_rescaleLin_apply
end P2MW
export P2MW.S_ModularCurve_periodMap_rescaleLin_apply (solution)
