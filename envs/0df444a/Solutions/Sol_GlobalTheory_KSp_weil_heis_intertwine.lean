-- Prove2me | solution 1 for GlobalTheory.KSp.weil_heis_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:41.454259+00:00
-- url     : https://prove2.me/submissions/617a6fa4-05aa-452a-8537-5504f4b93489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesWeylHeisenbergSchrodingerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicWeylElementGenerateUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicOperatorsHeisenbergCompatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationIntertwinesHeisenberg
import Theorems.Thm_GlobalTheory_SplitUnitary_heis_apply
import Theorems.Thm_GlobalTheory_T_fourier_intertwines_weyl_heisenberg_schrodinger
import Theorems.Thm_GlobalTheory_T_siegelParabolic_operators_heisenberg_compat
import Theorems.Thm_GlobalTheory_T_siegelParabolic_weylElement_generate_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hK
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ∀ w : Matrix α (ν ⊕ ν) E, Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * mat c g)}
      one_mem' := by
        intro w
        have h1 : mat c (1 : UG c (stdJ ν E)) = 1 := rfl
        rw [map_one, h1, Matrix.mul_one, mul_one, one_mul]
      mul_mem' := by
        intro g h hg hh w
        have hm : mat c (g * h) = mat c g * mat c h := rfl
        rw [map_mul, ← mul_assoc, hg, mul_assoc, hh, ← mul_assoc, hm, Matrix.mul_assoc]
      inv_mem' := by
        intro g hg w
        have h1 : mat c g⁻¹ * mat c g = 1 := by
          change (((g⁻¹ * g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
          rw [inv_mul_cancel]; rfl
        have h2 := hg (w * mat c g⁻¹)
        rw [Matrix.mul_assoc, h1, Matrix.mul_one] at h2
        have h3 : ω g⁻¹ * ω g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h4 : ω g * ω g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        show Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹)
        calc Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * (ω g * Heisenberg₂ c hψ Q w) * ω g⁻¹ := by
              simp only [← mul_assoc, h3, one_mul]
          _ = ω g⁻¹ * (Heisenberg₂ c hψ Q (w * mat c g⁻¹) * ω g) * ω g⁻¹ := by rw [h2]
          _ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹) := by simp only [mul_assoc, h4, mul_one] }
  have hsieg : sieg c ν ≤ U := by
    intro p hp w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.par p hp]
    exact GlobalTheory.T.siegelParabolic_operators_heisenberg_compat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη p hp w φ
  have hweyl : weyl c ν ∈ U := by
    intro w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.wey]
    have hs : ∀ f : Matrix α ν E → ℂ, heisFun c ψ Q w (κ • f) = κ • heisFun c ψ Q w f := by
      intro f; funext x; simp only [heisFun, Pi.smul_apply, smul_eq_mul]; ring
    rw [hs, GlobalTheory.T.fourier_intertwines_weyl_heisenberg_schrodinger F E c δ hE α ν Q hQ ψ μ w φ]
    rfl
  have hU := GlobalTheory.T.siegelParabolic_weylElement_generate_unitary F E c δ hE ν U hsieg hweyl
  intro g w
  have hg : g ∈ U := hU ▸ Subgroup.mem_top g
  exact hg w
end GlobalTheory.KSp
