-- Prove2me | solution 1 for GlobalTheory.PolarisedLattice.lattice_of_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:52.408438+00:00
-- url     : https://prove2.me/submissions/b1c57d32-4c51-4554-bfd4-942cc342f29d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.PolarisedLattice
namespace GlobalTheory.PolarisedLattice
theorem _root_.solution {L W : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] [NormedAddCommGroup W]
    [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℝ W]
    (E : LinearMap.BilinForm ℤ L) (hE : Function.Injective E) (P : L →+ W) (S : W → W →ₗ[ℂ] ℂ)
    (hS : ∀ a b, (S (P b) (P a)).im = E a b) (hr : Module.finrank ℤ L = Module.finrank ℝ W) :
    Function.Injective P ∧ DiscreteTopology P.range ∧ Submodule.span ℝ (Set.range P) = ⊤ := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let M : Matrix _ _ ℤ := Matrix.of fun i j => E (b i) (b j)
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, h0⟩ := exists_vecMul_eq_zero_iff.2 h
    have h1 : E (∑ i, v i • b i) = 0 := b.ext fun j => by
      have := congrFun h0 j
      simpa [M, vecMul, dotProduct] using this
    have h2 : ∑ i, v i • b i = 0 := hE (by rw [h1, map_zero])
    exact hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h2))
  have hdet' : (M.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [← Int.cast_det]; exact_mod_cast hdet
  have hli : LinearIndependent ℝ fun i => P (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    have : c ᵥ* M.map (Int.cast : ℤ → ℝ) = 0 := by
      funext j
      have h1 := congrArg (fun v => (S (P (b j)) v).im) hc
      simp only [map_sum, ← algebraMap_smul ℂ (c _) (P _), map_smul, map_zero, Complex.im_sum, smul_eq_mul,
        Complex.coe_algebraMap, Complex.im_ofReal_mul, hS, Complex.zero_im] at h1
      simpa [M, vecMul, dotProduct] using h1
    exact congrFun (eq_zero_of_vecMul_eq_zero hdet' this)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ W := by
    rw [← hr, Module.finrank_eq_card_chooseBasisIndex]
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => P (b i)) :=
    (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  let B := Module.Basis.mk hli htop
  have hB : Set.range B = Set.range fun i => P (b i) := by simp [B]
  have hrange : P.range = (Submodule.span ℤ (Set.range B)).toAddSubgroup := by
    have : Submodule.span ℤ (Set.range B) = LinearMap.range P.toIntLinearMap := by
      rw [hB, LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]; rfl
    rw [this]; rfl
  refine ⟨(injective_iff_map_eq_zero P).2 fun a ha => hE ?_, ?_, ?_⟩
  · rw [map_zero]
    refine LinearMap.ext fun c => ?_
    have := hS a c
    rw [ha, map_zero, Complex.zero_im] at this
    exact_mod_cast this.symm
  · rw [hrange]; infer_instance
  · exact eq_top_iff.2 (htop.trans (Submodule.span_mono (Set.range_comp_subset_range _ _)))
end GlobalTheory.PolarisedLattice
